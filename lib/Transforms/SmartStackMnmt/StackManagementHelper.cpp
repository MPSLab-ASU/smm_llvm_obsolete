//===- --------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements several methods that are used to extract functions,
// loops, or portions of a module from the rest of the module.
//
//===----------------------------------------------------------------------===//

#include <iostream>
#include <fstream>
#include <limits>
#include <queue>
#include <stack>
#include <utility>
#include <unordered_map>
#include <unordered_set>

#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Support/raw_ostream.h"

#include "FuncType.h"
#include "Graph.h"


using namespace llvm;

namespace {


    struct StackManagementHelperPass : public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	StackManagementHelperPass() : ModulePass(ID) {
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	// Instrument the program specified by mod with stack management helper functions that will collect the stack size of each function
	bool getWcgNodeWeights(Module &mod) {
	    LLVMContext &context = mod.getContext();

	    // Types
	    PointerType* ptrty_int8 = PointerType::get(IntegerType::get(context, 8), 0);
	    PointerType* ptrty_ptrint8 = PointerType::get(ptrty_int8, 0);

	    std::vector<Type*> call_args;
	    call_args.push_back(ptrty_ptrint8);
	    FunctionType* functy_inline_asm = FunctionType::get(
		    Type::getVoidTy(context), // Results
		    call_args, // Params
		    false); //isVarArg


	    // Global variables
	    GlobalVariable* gvar_sp_calling = mod.getGlobalVariable("_sp_calling");
	    assert(gvar_sp_calling);
	    GlobalVariable* gvar_func_name = mod.getGlobalVariable("_func_name");
	    assert(gvar_func_name);

	    // Functions
	    Function *func_main = mod.getFunction("main");
	    Function *func_get_func_stack_size = mod.getFunction("_get_func_stack_size");
	    Function *func_dump_func_stack_sizes = mod.getFunction("_dump_func_stack_sizes");

	    // Inline assembly
	    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

	    // Const values
	    ConstantInt* const_int64_0 = ConstantInt::get(context, APInt(64, StringRef("0"), 10));

	    // Call graph
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph();

	    // Get the pointer to the global variable which saves format string
	    std::vector<Constant*> const_ptr_indices;
	    const_ptr_indices.push_back(const_int64_0);
	    const_ptr_indices.push_back(const_int64_0);
	    //Constant* const_ptr_format = ConstantExpr::getGetElementPtr(gvar_format, const_ptr_indices);

	    // Step 1: Insert management helper functions
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second); 
		Function *fi = cgn->getFunction();
		// Skip external nodes
		if (!fi)
		    continue;
		// Skip library functions
		if (isLibraryFunction(fi))
		    continue;
		// Skip stack management helper functions
		if (isStackManagementHelperFunction(fi))
		    continue;

		// Process user-defined functions

		// Get or build a gloabal variable which saves the name of current function
		GlobalVariable* gvar_curfuncname = mod.getGlobalVariable("__func__." + fi->getName().str(), true);
		Constant* const_ptr_curfuncname; 
		if (!gvar_curfuncname) {
		    //errs() << "__func__." + fi->getName().str() << "\n";
		    ArrayType* arrayty_curfuncname =ArrayType::get(IntegerType::get(context, 8), fi->getName().size()+1);
		    Constant *const_curfuncname = ConstantDataArray::getString(context, fi->getName(), true);
		    gvar_curfuncname = new GlobalVariable(/*Module=*/mod,
			    /*Type=*/arrayty_curfuncname,
			    /*isConstant=*/true,
			    /*Linkage=*/GlobalValue::PrivateLinkage,
			    /*Initializer=*/0, // has initializer, specified below
			    /*Name=*/"__func__." + fi->getName());
		    gvar_curfuncname->setAlignment(1);
		    const_ptr_curfuncname = ConstantExpr::getGetElementPtr(gvar_curfuncname, const_ptr_indices);
		    gvar_curfuncname->setInitializer(const_curfuncname);
		}
		else
		    const_ptr_curfuncname = ConstantExpr::getGetElementPtr(gvar_curfuncname, const_ptr_indices);


		// Insert _get_stack_size() function before the first non-phi instruction in each function except main function
		//if (! (&*fi == func_main) ) {
		    Instruction *first_non_phi = fi->begin()->getFirstNonPHI();
		    new StoreInst(const_ptr_curfuncname, gvar_func_name, false, first_non_phi);
		    CallInst::Create(func_get_func_stack_size, "", first_non_phi);
		//}

		for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
		    // If we find a function call, read the current SP value and print out the caller's name
		    if (CallInst * call_func = dyn_cast<CallInst>(cgni->first)) {
			// Skip inline assembly
			if (call_func->isInlineAsm())
			    continue;
			Function *callee = call_func->getCalledFunction();
			// SKip if callee is a function pointer or a library function
			if(!callee) 
			    continue;
			if( isLibraryFunction(callee)) 
			    continue;
			if( isStackManagementHelperFunction(callee)) 
			    continue;
			// Read the current SP value
			CallInst::Create(func_getSP, gvar_sp_calling, "", call_func);
		    }
		}
	    }

	    // Step 2: transform the main function to an user-defined function (this step will destroy call graph, so it must be in the last)
	    // Create an external function called smm_main
	    Function *func_smm_main = Function::Create(cast<FunctionType>(func_main->getType()->getElementType()), func_main->getLinkage(), "smm_main", &mod);
	    ValueToValueMapTy VMap;
	    std::vector<Value*> args;

	    // Set up the mapping between arguments of main to those of smm_main
	    Function::arg_iterator ai_new = func_smm_main->arg_begin();
	    for (Function::arg_iterator ai = func_main->arg_begin(), ae = func_main->arg_end(); ai != ae; ++ai) { 
		ai_new->setName(ai->getName());
		VMap[ai] = ai_new;
		args.push_back(ai);
		ai_new++;
	    }
	    // Copy the function body from main to smm_main
	    SmallVector<ReturnInst*, 8> Returns;
	    CloneFunctionInto(func_smm_main, func_main, VMap, true, Returns);

	    // Delete all the basic blocks in main function
	    std::vector<BasicBlock*> bb_list;
	    for (Function::iterator bi = func_main->begin(), be = func_main->end();  bi!= be; ++bi) { 
		for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ++ii) {
		    ii->dropAllReferences(); //Make sure there are no uses of any instruction
		} 
		bb_list.push_back(bi);
	    }
	    for (unsigned int i = 0; i < bb_list.size(); ++i) {
		bb_list[i]->eraseFromParent();
	    }

	    // Create the new body of main function which calls smm_main and return 0
	    BasicBlock* entry_block = BasicBlock::Create(getGlobalContext(), "EntryBlock", func_main);
	    IRBuilder<> builder(entry_block);
	    // Read the current SP value
	    builder.CreateCall(func_getSP, gvar_sp_calling);
	    builder.CreateCall(func_smm_main, args);
	    Value *zero = builder.getInt32(0);
	    builder.CreateRet(zero);

	    // Insert starting and ending code in main function
	    for (Function::iterator bi = func_main->begin(), be = func_main->end(); bi != be; ++bi) {
		for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ii++) {
		    Instruction *inst  = &*ii;
		    if (inst->getOpcode() == Instruction::Ret) {
			CallInst::Create(func_dump_func_stack_sizes, "", inst);
		    }
		}
	    }

	    return true;
	}

	bool extractAnnotatedWcgPaths(Module &mod) {
	    long ssize;
	    std::string func_name;
	    std::ofstream ofs;
	    std::ifstream ifs;
	    std::unordered_map <std::string, long> wcg_nodes;
	    std::vector<std::vector<CallGraphNode::CallRecord *> > paths;
	    std::unordered_set <CallGraphNode *> uncertain_functions;
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph(); // call graph
	    CallGraphNode *cgn_main = cg[mod.getFunction("main")]; 
	    CallGraphNode::CallRecord *root;

	    // Initialize root node by main function
	    for (CallGraphNode::iterator cgni = cg.begin()->second->begin(), cgne = cg.begin()->second->end(); cgni != cgne; cgni++) {
		if (cgni->second == cgn_main) {
		    root = &*cgni;
		    break;
		}
	    }
	    assert(CallGraphNode::iterator(root) != cg.begin()->second->end());

	    // Get all the paths from the call graph rooted at main
	    auto res = extractPaths(root); 
	    paths = res.first;
	    uncertain_functions = res.second;

	    ifs.open("wcg_nodes.txt", std::fstream::in);
	    // Read function stack sizes
	    while (ifs.good()) {
		ifs >> func_name >> ssize;
		wcg_nodes[func_name]  = ssize;
	    }

	    /*
	    for (auto ii = wcg_nodes.begin(), ie = wcg_nodes.end(); ii != ie; ii++) {
		errs() << ii->first << " " << ii->second << "\n";
	    }
	    */

	    // Print out all the edges
	    ofs.open("wcg_paths.txt", std::fstream::out) ;
	    bfsPrint(root, paths, ofs);

	    ofs << "#\n";

	    // Print out annotated WCG paths
	    for (size_t i = 0; i < paths.size(); i++) {
		//ofs << "path" << i << " : ";
		for (size_t j = 0; j < paths[i].size(); j++) {
		    if (paths[i][j]->second->getFunction()) {
			std::string func_name = paths[i][j]->second->getFunction()->getName().str();
			// Print node name (function name)
			ofs << func_name << " ";
			// Print node weight (function stack size)
			if (wcg_nodes.find(func_name) != wcg_nodes.end())
			    ofs << wcg_nodes[func_name];
			else {
			    // TODO Get library function stack sizes
			    //errs() << func_name << "\n";
			    ofs << std::numeric_limits<int>::max();
			}
			ofs << " ";
			// Print edge weight (number of function calls)
			if (j < paths[i].size()-1)
			    ofs << "1";
			else
			    ofs << "0";
			ofs << " ";
		    }
		    else {
			ofs << "externalNode 0 ";
		    }
		}
		ofs << "\n";
	    }

	    ofs << "#\n";

	    // Print out uncertain function names
	    for (auto ii = uncertain_functions.begin(), ie = uncertain_functions.end(); ii != ie; ii++) {
		if ((*ii)->getFunction()) {
		    ofs << (*ii)->getFunction()->getName().str() << "\n";
		}
		else 
		    ofs << "externalNode\n";
	    }

	    ofs.close();
	    ifs.close();

	    return false;
	}

	virtual bool runOnModule(Module &mod) {
	    std::ifstream ifs;
	    std::ofstream ofs;
	    // Call graph
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph();

	    // Get stack frame sizes of user-defined functions
	    ifs.open("wcg_nodes.txt", std::fstream::in);
	    if (!ifs.good()) {
		errs() << "Dumping node weights of WCG to wcg_nodes.txt...\n";
		ifs.close();
		getWcgNodeWeights(mod);
	    }
	    /*
	    ifs.open("lib_funcs.txt", std::fstream::in);
	    if (!ifs.good()) {
		ifs.close();
		ofs.open("lib_funcs.txt", std::fstream::out);
		for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		    CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second);
		    Function *fi = cgn->getFunction();
		    // Skip external nodes
		    if (!fi)
			continue;
		    // Skip library functions
		    if (isLibraryFunction(fi))
			ofs << fi->getName().str() << "\n";
		}
		ofs.close();
	    }
	    */
	    else {

		errs() << "Dumping annotated paths of WCG to wcg_paths.txt...\n";
		ifs.close();
		extractAnnotatedWcgPaths(mod);
	    }


	    // Print out the names of library functionsa
	    ofs.open("lib_funcs.txt", std::fstream::out);
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second);
		Function *fi = cgn->getFunction();
		// Skip external nodes
		if (!fi)
		    continue;
		// Skip library functions
		if (isLibraryFunction(fi))
		    ofs << fi->getName().str() << "\n";
	    }
	    ofs.close();

	    return true;
	}
    };
}

char StackManagementHelperPass::ID = 0; //Id the pass.
static RegisterPass<StackManagementHelperPass> X("smmsmh", "Stack Management Helper Pass"); //Register the pass.

