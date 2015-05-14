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

#include <fstream>
#include <queue>
#include <tuple>
#include <stack>
#include <unordered_map>
#include <unordered_set>

#include "function.h"
#include "graph.h"
#include "instrumentation.h"

#define DEBUG

using namespace llvm;

namespace {

    struct SmartStackManagementPass : public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	SmartStackManagementPass() : ModulePass(ID) {
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	virtual bool runOnModule(Module &mod) {
	    LLVMContext &context = mod.getContext();

	    // Pointer Types
	    PointerType* ptrty_int8 = PointerType::get(IntegerType::get(context, 8), 0);
	    PointerType* ptrty_ptrint8 = PointerType::get(ptrty_int8, 0);
	    // Function Types
	    std::vector<Type*> call_args;
	    call_args.push_back(ptrty_ptrint8);
	    FunctionType* functy_inline_asm = FunctionType::get(
		    Type::getVoidTy(context), // Results
		    call_args, // Params
		    false); //isVarArg

	    // External Variables
	    GlobalVariable* gvar_spm_end = new GlobalVariable(mod, // Module
		    IntegerType::get(context, 8), //Type
		    false, //isConstant
		    GlobalValue::ExternalLinkage, // Linkage
		    0, // Initializer
		    "_spm_end");

	    // Global Variables
	    GlobalVariable* gvar_mem_stack_base = mod.getGlobalVariable("_mem_stack_base");
	    GlobalVariable* gvar_spm_stack_base = mod.getGlobalVariable("_spm_stack_base");
	    //GlobalVariable* gvar_spm_depth = mod.getGlobalVariable("_stack_depth");
	    //GlobalVariable* gvar_stack = mod.getGlobalVariable("_stack");

	    // Functions
	    Function *func_main = mod.getFunction("main");
	    //Function *func_g2l = mod.getFunction("_g2l");
	    //Function *func_l2g = mod.getFunction("_l2g");
	    Function *func_sstore = mod.getFunction("_sstore");
	    //Function *func_sload = mod.getFunction("_sload");

	    // Inline Assembly
	    InlineAsm *func_putSP = InlineAsm::get(functy_inline_asm, "mov $0, %rsp;", "*m,~{rsp},~{dirflag},~{fpsr},~{flags}",true);
	    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

	    // Call Graph 
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph(); // call graph
	    CallGraphNode *cgn_main = cg[mod.getFunction("main")];
	    CallGraphNode::CallRecord *root;
	    std::vector<std::vector<CallGraphNode::CallRecord *> > paths;
	    std::unordered_set <CallGraphNode *> undecidable_cgns;

	    //Step 0: extract all the paths from original call graph
	    // Initialize root node by main function
	    for (CallGraphNode::iterator cgni = cg.begin()->second->begin(), cgne = cg.begin()->second->end(); cgni != cgne; cgni++) {
		if (cgni->second == cgn_main) {
		    root = &*cgni;
		    break;
		}
	    }
	    assert(CallGraphNode::iterator(root) != cg.begin()->second->end());

	    // Step 0: Extarct all the paths from call graph rooted at main function
	    auto res = extractPaths(root);
	    paths = res.first;
	    undecidable_cgns = res.second;
#ifdef DEBUG
	    errs() <<  "Extract paths {\n";
	    // Print out all the paths
	    for (size_t i = 0; i < paths.size(); i++) {
		for (size_t j = 0; j < paths[i].size(); j++) {
		    if (paths[i][j]->second->getFunction())
			errs() << "\t" << paths[i][j]->first << " " << paths[i][j]->second->getFunction()->getName() << "\t";
		    else
			errs() << "\t" << paths[i][j]->first << " " << "externalNode" << "\t";
		}
		errs() << "\n";
	    }
	    errs() << "}\n\n";
#endif

	    // Step 1: get SSMD cuts
	    std::unordered_map <unsigned, std::vector <std::pair<unsigned, std::string> > > cuts;
	    // Read SSDM output file
	    std::ifstream ifs;
	    ifs.open("wcg_cuts.txt", std::fstream::in);
	    assert(ifs.good());
	    // Read function stack sizes
#ifdef DEBUG
	    errs() << "Reading SSDM output file...\n";
	    errs() << "{\n";
#endif
	    while (ifs.good()) {
		unsigned i, j;
		std::string func_name;
		ifs >> i >> j >> func_name;
		// Ignore white spaces after the last line
		if (func_name != "") {
#ifdef DEBUG		    
		    errs() << "\t" << i << " " << j << " " << func_name << "\n";
#endif
		    cuts[i-1].push_back( std::make_pair(j-1, func_name) );
		}
	    }
	    ifs.close();

#ifdef DEBUG
	    errs() << "}\n\n\n";
	    errs() << "Sorting SSDM cuts according to paths...\n";
	    errs() << "{\n";
#endif

	    // Sort cuts acoording to paths
	    for (auto cutsi = cuts.begin(), cutse = cuts.end(); cutsi != cutse; cutsi++) {
		std::sort(cutsi->second.begin(), cutsi->second.end());
#ifdef DEBUG
		errs() << "\tpath " << cutsi->first << " : ";
		for (size_t i = 0; i < cutsi->second.size(); i++)
		    errs() << cutsi->second[i].first << " " << cutsi->second[i].second << "  ";
		errs() << "\n";
#endif
	    }
#ifdef DEBUG
	    errs() << "}\n\n\n";
#endif


#ifdef DEBUG
	    errs() << "Pointer management functions instrumentation {\n";
#endif

#ifdef DEBUG
	    errs() << "Inserting g2l functions... {\n";
#endif
	    // Step 2: Insert g2l function calls
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = cgi->second;
		Function *fi = cgn->getFunction();
		// Skip external nodes
		if (!fi)
		    continue;
		// Skip library functions
		if (isLibraryFunction(fi))
		    continue;
		// Skip stack management functions
		if (isStackManagementFunction(fi))
		    continue;
		// Skip main function
		if (fi == func_main)
		    continue;
		// Process user-defined functions
		g2l_pointer_management_instrumentation(mod, cgn);
	    }
#ifdef DEBUG
	    errs() << "}";
#endif

#ifdef DEBUG
	    errs() << "Inserting l2g functions: {\n";
#endif
	    // Step 3: Insert l2g functions
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second); 
		Function *fi = cgn->getFunction();
		// Skip external nodes
		if (!fi)
		    continue;
#ifdef DEBUG
		errs() << "\t" << fi->getName() << "\n";
#endif
		// Skip library functions
		if (isLibraryFunction(fi))
		    continue;
		// Skip stack management functions
		if (isStackManagementFunction(fi))
		    continue;

		// Process user-defined functions
		l2g_pointer_management_instrumentation(mod, cgn);
	    }

#ifdef DEBUG
	    errs() << "}";
#endif

#ifdef DEBUG
	    errs() << "}\n\n\n";
#endif

#ifdef DEBUG
	    errs() << "Inserting management functions according to SSDM cuts: {\n";
#endif

	    // Step 4: Insert stack management functions
	    // Decide the insertion points of stack management function according to SSDM output
	    std::unordered_set <CallInst *> stack_management_insert_pts;
	    for (auto cuti = cuts.begin(), cute = cuts.end(); cuti != cute; cuti++) {
		for (size_t vi = 0; vi < cuti->second.size(); vi++) {
		    unsigned i, j;
		    std::string func_name;
		    i = cuti->first;
		    j = cuti->second[vi].first;
		    func_name = cuti->second[vi].second;
		    assert(paths[i][j]->first && paths[i][j]->second);
		    CallInst *call_inst = dyn_cast<CallInst> (paths[i][j]->first);
		    assert(call_inst);
		    stack_management_insert_pts.insert(call_inst);
		}
	    }
	    
	    // Insert stack management functions accroding to SSDM cuts
	    for (auto si = stack_management_insert_pts.begin(), se = stack_management_insert_pts.end(); si != se; si++) {
		CallInst *call_inst = *si;
		// Insert stack management functions
		stack_management_instrumentation(mod, call_inst);
	    }

#ifdef DEBUG
	    errs() << "}\n";
#endif

	    // Step 4: Insert management functions at self-recursive calls
#ifdef DEBUG
	    errs() << "Inserting management functions around recursive calls... {\n";
#endif
	    for (std::unordered_set <CallGraphNode *>::iterator si = undecidable_cgns.begin(), se = undecidable_cgns.end(); si != se; si++) {
		CallGraphNode * cgn = *si;
		// Skip external nodes
		if (!cgn->getFunction())
		    continue;
#ifdef DEBUG
		errs() << cgn->getFunction()->getName() << "\n";
#endif
		for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
		    // Skip non-self-recursive calls
		    if (cgni->second != cgn)
			continue;
		    CallInst *call_inst = dyn_cast<CallInst> (cgni->first);
		    assert(call_inst);

		    // Check if stack management functions have been inserted
		    BasicBlock::iterator ii(call_inst);
		    BasicBlock::iterator pos = ii;
		    long k = 0;
		    do {
			if (pos == ii->getParent()->begin())
			    break;
			pos--;
			k++;
		    } while(k < 2);

		    if (k >= 2) {
			CallInst *call_inst = dyn_cast<CallInst>(pos);
			if (call_inst && call_inst->getCalledFunction() == func_sstore)
			    continue;
		    }
		    // Insert stack management functions
		    stack_management_instrumentation(mod, call_inst);
		}
	    }

#ifdef DEBUG
	    errs() << "}\n";
#endif

	    // Step 4: transform the main function to an user-defined function (this step will destroy call graph, so it must be in the last)
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
	    builder.CreateCall(func_smm_main, args);
	    Value *zero = builder.getInt32(0);
	    builder.CreateRet(zero);

	    // Insert starting and ending code in main function
	    for (Function::iterator bi = func_main->begin(), be = func_main->end(); bi != be; ++bi) {
		for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ii++) {
		    Instruction *inst  = &*ii;
		    if (dyn_cast<CallInst>(inst)) {
			CallInst::Create(func_getSP, gvar_mem_stack_base, "", inst);
			new StoreInst(gvar_spm_end, gvar_spm_stack_base, "", inst);
			CallInst::Create(func_putSP, gvar_spm_stack_base, "", inst); 
		    }
		    else if (inst->getOpcode() == Instruction::Ret) {
			CallInst::Create(func_putSP, gvar_mem_stack_base, "", inst); 
		    }
		}
	    }

	    return true;
	}
    };
}

char SmartStackManagementPass::ID = 0; //Id the pass.
static RegisterPass<SmartStackManagementPass> X("smmssm", "Smart Stack Management Pass"); //Register the pass.

