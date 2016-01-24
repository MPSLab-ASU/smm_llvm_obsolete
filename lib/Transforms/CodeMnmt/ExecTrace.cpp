//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "smmcm-exec"

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/YAMLTraits.h"

#include <cassert>
#include <cmath>
#include <deque>
#include <fstream>
#include <iostream>
#include <set>
#include <stack>
#include <string>
#include <utility>
#include <vector>
#include <unordered_set>
#include <unordered_map>

#include "FuncType.h"
#include "Graph.h"


using namespace llvm;

namespace {
    struct ExecTrace : public ModulePass { // Insert code management functions
	static char ID; // Pass identification, replacement for typeid
	ExecTrace() : ModulePass(ID) {}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	    AU.addRequired<LoopInfo>();
	}


	virtual bool runOnModule (Module &mod) {
	    unsigned long code_size;
	    std::ifstream ifs;
	    std::ofstream ofs;
	    std::string func_name;
	    std::unordered_map <std::string, unsigned long> func_code_size;
	    std::unordered_map <BasicBlock *, std::deque<CallGraphNode::CallRecord *> > loop2call;
	    std::vector<Value*> call_args;
	    std::vector<CallGraphNode::CallRecord *> exec_trace;

	    CallGraphNode *cgn_main;
	    CallGraphNode::CallRecord *root;
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph(); 
	    LLVMContext &context = mod.getContext();
	    IRBuilder<> builder(context);

	    /* Get the execution trace: begin */

	    ifs.open ("_func_size", std::ifstream::in | std::ifstream::binary);
	    while (ifs.good()) {
		func_name.clear();
		code_size = 0;
		ifs >> func_name >> code_size;
		if (func_name.empty())
		    continue;
		func_code_size[func_name]  = code_size;
		errs() << func_name << " " << func_code_size[func_name] << "\n";
	    }

	    cgn_main = cg[mod.getFunction("main")];

	    // Extract all the paths from call graph root at main function
	    // Initialize root node by main function
	    for (CallGraphNode::iterator cgni = cg.begin()->second->begin(), cgne = cg.begin()->second->end(); cgni != cgne; cgni++) {
		if (cgni->second == cgn_main) {
		    root = &*cgni;
		    break;
		}
	    }
	    assert(CallGraphNode::iterator(root) != cg.begin()->second->end());

	    // Get the execution trace based on the call graph, starting from the main function
	    exec_trace = getExecTrace(root);

	    // Get the function calls within loops
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		if(CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second)) {
		    Function *fi = cgn->getFunction();
		    // Skip external nodes (inline functions and function pointers)
		    if(!fi)
			continue;
		    // Skip library functions
		    if (isLibraryFunction(fi))
			continue;
		    LoopInfo &lpi = getAnalysis<LoopInfo>(*fi);
		    for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
			CallInst *call_inst = dyn_cast <CallInst> (cgni->first);
			CallGraphNode *called_cgn = dyn_cast <CallGraphNode> (cgni->second);
			Function *callee = called_cgn->getFunction();
			assert(call_inst && called_cgn);
			// Skip external nodes (inline assemblies or function pointers)
			if (!callee)
			    continue;
			// Skip library functions
			if (isLibraryFunction(callee))
			    continue;
			Loop* lp = lpi.getLoopFor(call_inst->getParent());
			// Include function calls within child loops as function calls in current loop
			while (lp) {
			    BasicBlock *lp_header = lp->getHeader();
			    loop2call[lp_header].push_back(&*cgni);
			    lp = lp->getParentLoop();
			}
		    }
		}
	    }


	    // Print the execution trace with loop information
	    errs() << "Generating the execution trace...\n";
	    ofs.open ("_exec_trace", std::ofstream::out | std::ofstream::trunc | std::ofstream::binary);

	    /*
	    for (auto ii = loop2call.begin(), ie = loop2call.end(); ii != ie; ++ii) {
		CallGraphNode *cgn1 = ii->second.front()->second;
		CallGraphNode *cgn2 = ii->second.back()->second;
		ofs << ii->first << " " << ii->second.front() << " " << cgn1->getFunction()->getName().str() << " " << ii->second.back() << " " << cgn2->getFunction()->getName().str() << "\n";
	    }*/

	    for (auto ii = func_code_size.begin(), ie = func_code_size.end(); ii != ie; ii++) {
		ofs << ii->first << " " << ii->second << "\n";
	    }
	    ofs << "#\n";

	    long int lp_nest = 0;
	    for (size_t i = 0; i < exec_trace.size(); i++) {
		CallGraphNode::CallRecord *call_record = exec_trace[i];
		assert(call_record);
		CallGraphNode *called_cgn = call_record->second;
		Function *callee = called_cgn->getFunction();
		std::string callee_name = callee->getName().str();

		if (callee_name == "main") {
		    //ofs << callee_name << " " << func_code_size[callee_name] << " 1 ";
		    ofs << "main 1 ";
		    continue;
		}

		CallInst *call_inst = dyn_cast <CallInst> (call_record->first);
		BasicBlock *call_bb = call_inst->getParent();
		Function *caller = call_bb->getParent();
		LoopInfo &lpi = getAnalysis<LoopInfo>(*caller);
		Loop *lp = lpi.getLoopFor(call_bb);
		std::stack <BasicBlock *> lp_stack;

		// Found the start of a loop
		while (lp) {
		    BasicBlock *lp_header = lp->getHeader(); 
		    if (i > 0) {
			CallGraphNode * prev_cgn = dyn_cast<CallGraphNode>(exec_trace[i-1]->second);
			if (prev_cgn->getFunction() == lp_header->getParent() && call_record == loop2call[lp_header].front()) {
			    lp_stack.push(lp_header);
			}
		    }
		    lp = lp->getParentLoop();
		}

		while (lp_stack.size() > 0) {
		    ++lp_nest;
		    ofs << "{" << lp_stack.top() << " " << lp_nest << " ";
		    lp_stack.pop();
		}

		// The information of the current function being visited
		ofs << callee_name << " " << (unsigned long)pow(10, (double)lp_nest) << " ";

		lp = lpi.getLoopFor(call_bb);

		// Found the end of a loop
		while (lp) {
		    BasicBlock *lp_header = lp->getHeader(); 
		    if (i < exec_trace.size()-1) {
			CallGraphNode * next_cgn = dyn_cast<CallGraphNode>(exec_trace[i+1]->second);
			if (call_record == loop2call[lp_header].back() && next_cgn->getFunction() == lp_header->getParent()) {
			    ofs << "}" << lp_header << " " << lp_nest << " ";
			    --lp_nest;
			    assert(lp_nest >= 0);
			}
		    } 
		    lp = lp->getParentLoop();
		}

	    } 

	    ofs << "\n";
	    ofs.close();
	    errs() << "The execution trace is generated!\n";

	    /* Get the execution trace: end */

	    return false;
	}

    };
}

char ExecTrace::ID = 0;
static RegisterPass<ExecTrace> X("smmcm-exec", "Emulation of Execution)");
