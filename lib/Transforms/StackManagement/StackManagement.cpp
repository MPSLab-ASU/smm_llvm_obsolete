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

using namespace llvm;

namespace {

    struct StackManagerPass : public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	StackManagerPass() : ModulePass(ID) {
	}

	// Checks whether a function is a library function (including intrinsic functions)
	inline bool isLibraryFunction(Function *func) {
	    return (func->isDeclaration()); 
	}

	// Check if a function is stack management function	
	inline bool isStackManagementFunction(Function *func) {
	    if (func->getName().count("_g2l") ==1)
		return true;
	    if (func->getName().count("_l2g") ==1)
		return true;
	    if (func->getName().count("_sstore") ==1)
		return true;
	    if (func->getName().count("_sload") ==1)
		return true;
	    if (func->getName().count("dma") ==1) {
		return true;
	    }

	    return false;
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
	    GlobalVariable* gvar_spm_depth = mod.getGlobalVariable("_stack_depth");
	    GlobalVariable* gvar_stack = mod.getGlobalVariable("_stack");

	    // Functions
	    Function *func_main = mod.getFunction("main");
	    Function *func_g2l = mod.getFunction("_g2l");
	    Function *func_l2g = mod.getFunction("_l2g");
	    Function *func_sstore = mod.getFunction("_sstore");
	    Function *func_sload = mod.getFunction("_sload");

	    // Inline Assembly
	    InlineAsm *func_putSP = InlineAsm::get(functy_inline_asm, "mov $0, %rsp;", "*m,~{rsp},~{dirflag},~{fpsr},~{flags}",true);
	    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

	    // Step 1: transform the main function to an user-defined function
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

	    // Step 2 : Add noinline attributes to functions
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		if (fi->hasFnAttribute(Attribute::NoInline) || fi->hasFnAttribute(Attribute::AlwaysInline) )
		    continue;
		fi->addFnAttr(Attribute::NoInline);
	    }


	    // Step 3: Insert l2g functions
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		
		//errs() << fi->getName() << "\n";

		Function *caller = &*fi;
		// Skip if it is a library function
		if (isLibraryFunction(caller))
		    continue;
		// Skip if it is a stack management function
		if (isStackManagementFunction(caller))
		    continue;
		// Skip if it is main function
		if (&*fi == func_main)
		    continue;
		// We have found an user-defined function (including main function)
		for (Function::iterator bi = fi->begin(), be = fi->end(); bi != be; ++bi) {
		    for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ii++) {
			Instruction *inst = ii;
			if (CallInst *call_func = dyn_cast<CallInst>(inst)) {
			    // Skip if an inline asm is called
			    if (call_func->isInlineAsm())
				continue;
			    Function *callee = call_func->getCalledFunction();
			    // If the callee is a function pointer, skip the check and insert management functions
			    if (callee) { // If callee is not a function pointer
				//Skip if a stack management function is called
				if (isStackManagementFunction(callee))
				    continue;
				//Skip if an intrinsic function is called
				if (callee->isIntrinsic())
				    continue;
			    } 
			    for (unsigned int i = 0, n = call_func->getNumArgOperands(); i < n; i++) { // We have found function calls wth address arguments
				Value *operand = call_func->getArgOperand(i);
				if (operand->getType()->isPointerTy() ) {
				    IRBuilder<> builder(call_func); // Instruction will be inserted before ii
				    Value *cast_to = builder.CreatePointerCast(operand, Type::getInt8PtrTy(context), "cast_to_char_pointer"); // Cast the value (in this case, a memory address) to be of char pointer type required by l2g function
				    Value *call_l2g = builder.CreateCall(func_l2g, cast_to, "l2g_on_char_pointer"); // Call the function l2g with the value with cast type
				    Value *cast_from = builder.CreatePointerCast(call_l2g, operand->getType(), "cast_from_result"); // Cast the result back to be of the original type
				    for (unsigned int i = 0; i < call_func->getNumOperands(); i++) {
					if (call_func->getOperand(i) == operand ) // Replace the use of the original memory address with the translated address
					    call_func->setOperand(i, cast_from); // Replace the use of the original memory address with the translated address
				    }
				}
			    }

			}
		    }
		}
	    }

	    // TODO: Step 4: Insert g2l function calls
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		//errs() << fi->getName() << "\n";
		Function *caller = &*fi;
		// Skip if it is a library function
		if (isLibraryFunction(caller))
		    continue;
		// Skip if it is a stack management function
		if (isStackManagementFunction(caller))
		    continue;
		// Skip if it is main function
		if (&*fi == func_main)
		    continue;
		errs() << fi->getName() << " has " << (fi->isVarArg() ? "variable": "fixed") << " number of arguments\n";
		errs() << "\t" << *fi->getFunctionType() << "\n";
		// We have found a user-defined function
		for (Function::arg_iterator ai = fi->arg_begin(), ae = fi->arg_end(); ai != ae; ai++) {
		    if (ai->getType()->isPointerTy()) { // We have found a pointer argument
			errs() << "\t" << ai->getName() << " : " << *ai->getType() << "\n";
			for (Value::user_iterator ui = ai->user_begin(), ue = ai->user_end(); ui != ue; ++ui) {
			    if (Instruction *user_inst = dyn_cast<Instruction>(*ui)) { // Find an user instruction of the pointer argument
				errs() << "\t\t" << *user_inst << "\n";
				if (PHINode *target = dyn_cast<PHINode>(user_inst)) { // If the user instruction a phi instruction
				    for (unsigned int i = 0; i < target->getNumIncomingValues(); i++) {
					if(target->getIncomingValue(i) == ai) { // Find the use of the pointer argument
					    IRBuilder<> builder(target->getIncomingBlock(i)->getTerminator()); // Instruction will be inserted before this instruction
					    Value *cast_to = builder.CreatePointerCast(ai, Type::getInt8PtrTy(context), "cast_to_char_pointer"); // Cast the value (in this case, a memory address) to be of char pointer type required by l2g function
					    Value *call_g2l = builder.CreateCall(func_g2l, cast_to, "g2l_on_char_pointer"); // Call the function l2g with the value with cast type
					    Value *cast_from = builder.CreatePointerCast(call_g2l, ai->getType(), "cast_from_result"); // Cast the result back to be of the original type
					    // Replace the use of pointer argument (At most one use in phi instruction)
					    for (unsigned int j = 0; j < user_inst->getNumOperands(); j++) {
						if (user_inst->getOperand(j) == ai) {
						    user_inst->setOperand(j, cast_from);
						}
					    }
					}

				    }
				} else { // If the user instruction is not a phi instruction
				    IRBuilder<> builder(user_inst); // Instruction will be inserted before this instruction
				    Value *cast_to = builder.CreatePointerCast(ai, Type::getInt8PtrTy(context), "cast_to_char_pointer"); // Cast the value (in this case, a memory address) to be of char pointer type required by l2g function
				    Value *call_g2l = builder.CreateCall(func_g2l, cast_to, "g2l_on_char_pointer"); // Call the function l2g with the value with cast type
				    Value *cast_from = builder.CreatePointerCast(call_g2l, ai->getType(), "cast_from_result"); // Cast the result back to be of the original type
				    // Replace the uses of the pointer argument
				    for (unsigned int i = 0; i < user_inst->getNumOperands(); i++) {
					if (user_inst->getOperand(i) == ai ) 
					    user_inst->setOperand(i, cast_from); 
				    }
				}
			    }
			}
		    }
		}

	    }


	    // Step 5: Insert management functions
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		Function *caller = &*fi;
		//Skip if it is a library function
		if (isLibraryFunction(caller))
		    continue;
		// Skip if it is a stack management function
		if (isStackManagementFunction(caller))
		    continue;
		// Ignore if it is main function
		if (&*fi == func_main)
		    continue;
		// We have found an user-defined function (including main function)
		for (inst_iterator in = inst_begin(fi), ii=in++, ie = inst_end(fi); ii != ie; ii=in++) {
		    Instruction *inst = &*ii;
		    Instruction *next_inst = &*in;
		    if (CallInst * call_func = dyn_cast<CallInst>(inst)) { // We have found a function call
			// Skip if a inline asm is called
			if (call_func->isInlineAsm())
			    continue;
			Function *callee = call_func->getCalledFunction();
			// If the callee is a function pointer, skip the check and insert management functions
			if(callee) { // The callee is not a function pointer
			    // Skip if a management function is called
			    if (isStackManagementFunction(callee))
				continue;
			    // Skip if an llvm intrinsic is called
			    if (callee->isIntrinsic())
				continue;
			} 

			// Before the function call
			//	Insert a sstore function
			CallInst::Create(func_sstore, "", inst);
			// 	Insert putSP(_spm_stack_base)
			CallInst::Create(func_putSP, gvar_spm_stack_base, "", inst);
			// After the function call
			// 	Read value of _stack_depth after the function call
			LoadInst* val__spm_depth = new LoadInst(gvar_spm_depth, "", false, next_inst);
			ConstantInt* const_int32_0 = ConstantInt::get(context, APInt(32, StringRef("0"), 10));
			ConstantInt* const_int64_1 = ConstantInt::get(context, APInt(64, StringRef("1"), 10));
			// 	Calculate _stack_depth - 1
			BinaryOperator* val__spm_depth1 = BinaryOperator::Create(Instruction::Sub, val__spm_depth, const_int64_1, "sub", next_inst);
			// 	Get the address of _stack[_stack_depth-1]
			std::vector<Value*> ptr_arrayidx_indices;
			ptr_arrayidx_indices.push_back(const_int32_0);
			ptr_arrayidx_indices.push_back(val__spm_depth1);
			Instruction* ptr_arrayidx = GetElementPtrInst::Create(gvar_stack, ptr_arrayidx_indices, "arrayidx", next_inst);
			// 	Get the address of _stack[_stack_depth-1].spm_address
			std::vector<Value*> ptr_spm_addr_indices;
			ptr_spm_addr_indices.push_back(const_int32_0);
			ptr_spm_addr_indices.push_back(const_int32_0);
			Instruction* ptr_spm_addr = GetElementPtrInst::Create(ptr_arrayidx, ptr_spm_addr_indices, "spm_addr", next_inst);
			// 	Insert putSP(_stack[_stack_depth-1].spm_addr)
			CallInst::Create(func_putSP, ptr_spm_addr, "", next_inst);
			// 	Insert a corresponding sload function
			CallInst::Create(func_sload, "", next_inst);

			// Check if the function has return value
			Type * retty = call_func->getType();
			if (retty->isVoidTy())
			    continue;
			// Save return value in a global variable temporarily until sload is executed if it is used
			GlobalVariable *gvar = NULL; // Always create a new global variable in case of recursive functions

			for (Value::user_iterator ui_ret = call_func->user_begin(), ue_ret = call_func->user_end(); ui_ret != ue_ret; ++ui_ret) {
			    if (Instruction *user_inst = dyn_cast<Instruction>(*ui_ret)) { // We have found the use of return value
				if (!gvar) {
				    gvar = new GlobalVariable(mod, //Module
					    retty, //Type
					    false, //isConstant
					    GlobalValue::ExternalLinkage, //linkage
					    0, // Initializer
					    "_gvar"); //Name
				    // Initialize the temporary global variable
				    gvar->setInitializer(Constant::getNullValue(retty));
				    // Save return value to the global variable before sload is called
				    StoreInst *st_ret = new StoreInst(call_func, gvar);
				    st_ret->insertAfter(call_func);
				}

				if (PHINode *target = dyn_cast<PHINode>(user_inst)) { // Return value is used in a phi instruction
				    for (unsigned int i = 0; i < target->getNumIncomingValues(); i++) {
					if(target->getIncomingValue(i) == call_func) {
					    // Read the global variable
					    LoadInst *restore_ret = new LoadInst(gvar, "", target->getIncomingBlock(i)->getTerminator());
					    // Find the use of return value and replace it (At most one use in phi instruction)
					    for (unsigned int j = 0; j < user_inst->getNumOperands(); j++) {
						if (user_inst->getOperand(j) == call_func) {
						    user_inst->setOperand(j, restore_ret);
						}
					    }
					}

				    }
				} else { // Return value is used in a non-phi instruction
				    // Read the global variable
				    LoadInst *restore_ret = new LoadInst(gvar, "", user_inst);
				    // Find the uses of return value and replace them
				    for (unsigned int i = 0; i < user_inst->getNumOperands(); i++) {
					if (user_inst->getOperand(i) == call_func) { 
					    user_inst->setOperand(i, restore_ret);
					}
				    }
				}
			    }
			}
		    }
		}
	    }

	    return true;
	}
    };
}

char StackManagerPass::ID = 0; //Id the pass.
static RegisterPass<StackManagerPass> X("smmstack", "Stack Management Pass"); //Register the pass.

