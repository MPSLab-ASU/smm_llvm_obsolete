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

#include "function.h"
#include "instrumentation.h"


#define DEBUG

using namespace llvm;

namespace {

    struct StackManagementPass : public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	StackManagementPass() : ModulePass(ID) {
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	virtual bool runOnModule(Module &mod) {
	    LLVMContext &context = mod.getContext();

	    // Pointer Types
	    PointerType* ptrty_int8 = PointerType::get(IntegerType::get(context, 8), 0);
	    PointerType* ptrty_ptrint8 = PointerType::get(ptrty_int8, 0);

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
	    GlobalVariable* gvar_spm_depth = mod.getGlobalVariable("_stack_depth");
	    GlobalVariable* gvar_stack = mod.getGlobalVariable("_stack");

	    // Functions
	    Function *func_main = mod.getFunction("main");
	    Function *func_sstore = mod.getFunction("_sstore");
	    Function *func_sload = mod.getFunction("_sload");

	    // Inline Assembly
	    InlineAsm *func_putSP = InlineAsm::get(functy_inline_asm, "mov $0, %rsp;", "*m,~{rsp},~{dirflag},~{fpsr},~{flags}",true);
	    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

	    // Call graph
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph();


	    // Step 1:  Find uses of pointers and call l2g or g2l accordingly
	    // Find uses of stack variables
#ifdef DEBUG
	    errs() << "Pointer management functions instrumentation {\n";
#endif


#ifdef DEBUG
	    errs() << "g2l function instrumentation {\n";
#endif
	    // Step 2: Insert pointer management functions
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = cgi->second;
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
		// Skip main function
		if (fi == func_main)
		    continue;
		// Insert g2l functions
		g2l_pointer_management_instrumentation(mod, cgn);
	    }


#ifdef DEBUG
	    errs() << "l2g function instrumentation {\n";
#endif
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		if(CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second)) {
		    Function *fi = cgn->getFunction();
		    // Skip external nodes
		    if(!fi)
			continue;
		    // Skip library functions
		    if (isLibraryFunction(fi))
			continue;
		    // Skip management functions
		    if (isStackManagementFunction(fi))
			continue;
		    // insert l2g functions
		    l2g_pointer_management_instrumentation(mod, cgn);
		}
	    }

#ifdef DEBUG
	    errs() << "}\n\n\n";
#endif

#ifdef DEBUG
	    errs() << "Stack management functions instrumentation: {\n";
#endif

	    // Step 2: Insert management functions
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second); 
		Function *fi = cgn->getFunction();
		// Skip external nodes
		if (!fi)
		    continue;
		//Skip library functions
		if (isLibraryFunction(fi))
		    continue;
		// Skip stack management functions
		if (isStackManagementFunction(fi))
		    continue;

#ifdef DEBUG
		errs() << fi->getName() << "\n";
#endif
		// Process user-defined functions
		for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
		    // Insert management functions around function calls
		    if (CallInst *call_inst = dyn_cast<CallInst>(cgni->first)) {
			Instruction *inst = dyn_cast<Instruction>(cgni->first);
			BasicBlock::iterator ii(inst);
			Instruction *next_inst = &*(++ii);
			BasicBlock::iterator in(next_inst);
			assert(in != call_inst->getParent()->end());

			// Skip inline assebmly
			if (call_inst->isInlineAsm())
			    continue;
			Function *callee = call_inst->getCalledFunction();
			// If the callee is a function pointer or not a management function and an instrinsic function, go ahead and process
			if(callee) { 
			    if (isStackManagementFunction(callee))
				continue;
			    if (callee->isIntrinsic())
				continue;
			} 

			// Before the function call
			// Insert a sstore function
			CallInst::Create(func_sstore, "", inst);
			// Insert putSP(_spm_stack_base)
			CallInst::Create(func_putSP, gvar_spm_stack_base, "", inst);
			// After the function call
			// Read value of _stack_depth after the function call
			LoadInst* val__spm_depth = new LoadInst(gvar_spm_depth, "", false, next_inst);
			ConstantInt* const_int32_0 = ConstantInt::get(context, APInt(32, StringRef("0"), 10));
			ConstantInt* const_int64_1 = ConstantInt::get(context, APInt(64, StringRef("1"), 10));
			// Calculate _stack_depth - 1
			BinaryOperator* val__spm_depth1 = BinaryOperator::Create(Instruction::Sub, val__spm_depth, const_int64_1, "sub", next_inst);
			// Get the address of _stack[_stack_depth-1]
			std::vector<Value*> ptr_arrayidx_indices;
			ptr_arrayidx_indices.push_back(const_int32_0);
			ptr_arrayidx_indices.push_back(val__spm_depth1);
			Instruction* ptr_arrayidx = GetElementPtrInst::Create(gvar_stack, ptr_arrayidx_indices, "arrayidx", next_inst);
			// Get the address of _stack[_stack_depth-1].spm_address
			std::vector<Value*> ptr_spm_addr_indices;
			ptr_spm_addr_indices.push_back(const_int32_0);
			ptr_spm_addr_indices.push_back(const_int32_0);
			Instruction* ptr_spm_addr = GetElementPtrInst::Create(ptr_arrayidx, ptr_spm_addr_indices, "spm_addr", next_inst);
			// Insert putSP(_stack[_stack_depth-1].spm_addr)
			CallInst::Create(func_putSP, ptr_spm_addr, "", next_inst);
			// Insert a corresponding sload function
			CallInst::Create(func_sload, "", next_inst);

			// Skip if the function does not have return value
			Type * retty = call_inst->getType();
			if (retty->isVoidTy())
			    continue;
			// Skip if the return value is never used
			if (call_inst->getNumUses() == 0)
			    continue;
			// Save return value in a global variable temporarily until sload is executed if it is used
			// Always create a new global variable in case of recursive functions
			GlobalVariable *gvar = new GlobalVariable(mod, //Module
				retty, //Type
				false, //isConstant
				GlobalValue::ExternalLinkage, //linkage
				0, // Initializer
				"_gvar"); //Name
			// Initialize the temporary global variable
			gvar->setInitializer(Constant::getNullValue(retty));
			// Save return value to the global variable before sload is called
			StoreInst *st_ret = new StoreInst(call_inst, gvar);
			st_ret->insertAfter(call_inst);

#ifdef DEBUG
			errs() << "\t" << *call_inst <<  " " << call_inst->getNumUses() << "\n";
#endif
			for (Value::use_iterator ui_ret = call_inst->use_begin(), ue_ret = call_inst->use_end(); ui_ret != ue_ret;) {
			    // Move iterator to next use before the current use is destroyed
			    Use *u = &*ui_ret++;
			    Instruction *user_inst = dyn_cast<Instruction>(u->getUser()); 
			    assert(user_inst);
#ifdef DEBUG
			    errs() <<  "\t\t" << *user_inst << "\n";
#endif
			    if (StoreInst *st_inst = dyn_cast <StoreInst> (user_inst)) {
				if (st_inst->getPointerOperand()->getName().count("_gvar") == 1) {
#ifdef DEBUG
				    errs() << "\t\t\t" << st_inst->getPointerOperand()->getName() << "\n";
#endif
				    continue;
				}
			    }

			    Instruction *insert_point = user_inst;

			    if (PHINode *phi_inst = dyn_cast<PHINode>(user_inst))
				insert_point = phi_inst->getIncomingBlock(u->getOperandNo())->getTerminator();

			    // Read the global variable
			    LoadInst *ret_val = new LoadInst(gvar, "", insert_point);
			    // Find the uses of return value and replace them
			    u->set(ret_val);
			}
		    }
		}
	    }

#ifdef DEBUG
	    errs() << "}\n\n";
#endif
	    // Step 3: transform the main function to an user-defined function (this step will destroy call graph, so it must be in the last)
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

char StackManagementPass::ID = 0; //Id the pass.
static RegisterPass<StackManagementPass> X("smmsm", "Stack Management Pass"); //Register the pass.

