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
#include "llvm/IR/InlineAsm.h"
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
	inline bool isManagementFunction(Function *func) {
	    if (func->getName().count("_g2l") ==1)
		return true;
	    if (func->getName().count("_l2g") ==1)
		return true;
	    if (func->getName().count("_sstore") ==1)
		return true;
	    if (func->getName().count("_sload") ==1)
		return true;
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

	    // Step 1: transform the main function to an user function
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


	    // Step 2: Transform the functions with address arguments to pass pointers instead
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		Function *caller = &*fi;
		// Ignore library functions
		if (isLibraryFunction(caller))
		    continue;
		// Ignore stack management functions
		if (isManagementFunction(caller))
		    continue;
		// Ignore main function
		if (&*fi == func_main)
		    continue;
		// We have found an user function (including main function)
		for (Function::iterator bi = fi->begin(), be = fi->end(); bi != be; ++bi) {
		    for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ii++) {
			Instruction *inst = ii;
			if (CallInst *funcCall = dyn_cast<CallInst>(inst)) {
			    // Continue if inline asm is called
			    if (funcCall->isInlineAsm())
				continue;
			    Function *callee = funcCall->getCalledFunction();
			    //Continue if library management functions are called
			    //if (isLibraryFunction(callee))
				//continue;
			    //Continue if stack management functions are called
			    if (isManagementFunction(callee))
				continue;
			    for (unsigned int i = 0, n = funcCall->getNumArgOperands(); i < n; i++) { // We have found function calls wth address arguments
				Value *operand = funcCall->getArgOperand(i);
				if (operand->getType()->isPointerTy() ) {
				    // Create a pointer variable for each address argument
				    //AllocaInst* ptr = new AllocaInst(operand->getType(), "ptr", inst);
				    // Always create a new global variable
				    GlobalVariable *ptr = new GlobalVariable(mod, //Module
					    operand->getType(), //Type
					    false, //isConstant
					    GlobalValue::ExternalLinkage, //linkage
					    0, // Initializer
					    "_ptr"); //Name
				    // Initialize the temporary global variable
				    //gvar->setInitializer(Constant::getNullValue(retty));
				    ptr->setInitializer(Constant::getNullValue(operand->getType()));
				    //errs() << "inst: " << *inst << " operand: "<< *operand << "\n"; 
				    // Assign the pointer with the address
				    new StoreInst(operand, ptr, inst);
				    // Replace the address with corresponding pointer
				    LoadInst *ptrval = new LoadInst(ptr, "", inst);
				    funcCall->setOperand(i, ptrval);
				}
			    }
			}
		    }
		}
	    }

	    // Step 3: Insert l2g and g2l function
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		Function *caller = &*fi;
		// Ignore library functions
		if (isLibraryFunction(caller))
		    continue;
		// Ignore stack management functions
		if (isManagementFunction(caller))
		    continue;
		// Ignore main function
		if (&*fi == func_main)
		    continue;
		// We have found an user function (including main function)
		for (Function::iterator bi = fi->begin(), be = fi->end(); bi != be; ++bi) {
		    for (BasicBlock::iterator in=bi->begin(), ii=in++, ie = bi->end(); ii != ie; ii=in++) {
			Instruction *inst = ii;
			Instruction *nextInst = in;
			ii = inst;

			// Identify definition of pointers
			if (inst->getOpcode() == Instruction::Store) {
			    Value *operand0 = inst->getOperand(0);
			    Value *operand1 = inst->getOperand(1);
			    if (operand1->getType()->isPointerTy() && operand1->getType()->getPointerElementType()->isPointerTy()) {
				//We have found a pointer to stack data on the LHS, we need to wrap the RHS in a l2g function call.  The RHS is not a function argument.
				IRBuilder<> builder(ii); // Instruction will be inserted before ii
				// Take the data on the RHS and cast it to void * so it can be passed ot our function l2g
				Value *castToCharStar = builder.CreatePointerCast(operand0, Type::getInt8PtrTy(context), "castToChar*");
				// Call the function l2g and pass the void * data as a parameter to the function
				Value *call_l2g = builder.CreateCall(func_l2g, castToCharStar, "call_l2g");
				// Take the result from the function call and cast it to its previous type.
				Value *castFromCharStar = builder.CreatePointerCast(call_l2g, operand0->getType(), "castFromChar*");
				// Assign the result to the LHS of the original instruction.
				builder.CreateStore(castFromCharStar, operand1);
				// Delete the original instruction.
				//(ii++)->eraseFromParent();                                                              
				ii->eraseFromParent();                                                              
			    }
			}
			// Identify deference of pointers
			else if (inst->getOpcode() == Instruction::Load) {
			    Value *operand0 = inst->getOperand(0);
			    if (operand0->getType()->isPointerTy() && operand0->getType()->getPointerElementType()->isPointerTy()) {
				if ( nextInst->getOpcode() == Instruction::Load && nextInst->getOperand(0) == inst) {
				    // We have found a dereference of a pointer.  The next instruction is a load instruction and the current instructions value is the operand for the next instruction.
				    //errs() << fi->getName() << ": " << inst << " [" << *inst << "]\n\t is used in next instruction:[" << *nextInst <<"] as operand 0 " << nextInst->getOperand(0) << " ("<< *nextInst->getOperand(0) <<")\n";
				    IRBuilder<> builder(nextInst);
				    Value *castToCharStar = builder.CreatePointerCast(inst, Type::getInt8PtrTy(context), "castToChar*");
				    Value *call_g2l = builder.CreateCall(func_g2l, castToCharStar, "call_g2l");
				    Value *castFromCharStar = builder.CreatePointerCast(call_g2l, nextInst->getOperand(0)->getType(), "castFromChar*");
				    nextInst->setOperand(0, castFromCharStar);
				} else if (nextInst->getOpcode() == Instruction::Store && nextInst->getOperand(1) == inst) {
				    // We have found a dereference of a pointer.  The next instruction is a store instruction and the current instructions value is the operand for the next instruction.
				    //errs() << fi->getName() << ": " << inst << " [" << *inst << "]\n\t is used in next instruction:[" << *nextInst <<"] as operand 1 " << nextInst->getOperand(1) << " ("<< *nextInst->getOperand(1) <<")\n";
				    IRBuilder<> builder(nextInst);
				    Value *castToCharStar = builder.CreatePointerCast(inst, Type::getInt8PtrTy(context), "castToChar*");
				    Value *call_g2l = builder.CreateCall(func_g2l, castToCharStar, "call_g2l");
				    Value *castFromCharStar = builder.CreatePointerCast(call_g2l, nextInst->getOperand(1)->getType(), "castFromChar*");
				    nextInst->setOperand(1, castFromCharStar);
				}
			    }
			}
		    }
		}
	    }

	    // Step 4: Insert management functions
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		    Function *caller = &*fi;
		    //errs() << caller << " : " <<caller->getName() << " is " << (isLibraryFunction(caller)? "a": "not a") << " library function,";
		    //errs() << " is " << (isManagementFunction(caller)?"a":"not a") << " management function,";
		    //errs() << " is "  << ((caller == func_main )?"": "not") << " main function." << "\n";
		    //Ignore library functions
		    if (isLibraryFunction(caller))
			continue;
		    // Ignore stack management functions
		    if (isManagementFunction(caller))
			continue;
		    // Ignore main function
		    if (&*fi == func_main)
			continue;
		    // We have found an user function (including main function)
		    for (Function::iterator bi = fi->begin(), be = fi->end(); bi != be; ++bi) {
			for (BasicBlock::iterator in = bi->begin(), ii=in++, ie = bi->end(); ii != ie; ii=in++) {
			Instruction *inst = ii;
			Instruction *nextInst = in;
			ii = inst;
			if (CallInst * funcCall = dyn_cast<CallInst>(inst)) { // We found a function call
			    // Ignore inline asm
			    if (funcCall->isInlineAsm())
				continue;
			    Function *callee = funcCall->getCalledFunction();
			    //Continue if library management functions are called
			    //if (isLibraryFunction(callee))
				//continue;
			    // Ignore it if the callee is a management function
			    if (isManagementFunction(callee))
				continue;
			    // Before the function call
			    //	Insert a sstore function
			    CallInst::Create(func_sstore, "", inst);
			    // 	Insert putSP(_spm_stack_base)
			    CallInst::Create(func_putSP, gvar_spm_stack_base, "", inst);
			    // After the function call
			    // 	Read value of _stack_depth after the function call
			    LoadInst* val__spm_depth = new LoadInst(gvar_spm_depth, "", false, nextInst);
			    ConstantInt* const_int32_0 = ConstantInt::get(context, APInt(32, StringRef("0"), 10));
			    ConstantInt* const_int64_1 = ConstantInt::get(context, APInt(64, StringRef("1"), 10));
			    // 	Calculate _stack_depth - 1
			    BinaryOperator* val__spm_depth1 = BinaryOperator::Create(Instruction::Sub, val__spm_depth, const_int64_1, "sub", nextInst);
			    // 	Get the address of _stack[_stack_depth-1]
			    std::vector<Value*> ptr_arrayidx_indices;
			    ptr_arrayidx_indices.push_back(const_int32_0);
			    ptr_arrayidx_indices.push_back(val__spm_depth1);
			    Instruction* ptr_arrayidx = GetElementPtrInst::Create(gvar_stack, ptr_arrayidx_indices, "arrayidx", nextInst);
			    // 	Get the address of _stack[_stack_depth-1].spm_address
			    std::vector<Value*> ptr_spm_addr_indices;
			    ptr_spm_addr_indices.push_back(const_int32_0);
			    ptr_spm_addr_indices.push_back(const_int32_0);
			    Instruction* ptr_spm_addr = GetElementPtrInst::Create(ptr_arrayidx, ptr_spm_addr_indices, "spm_addr", nextInst);
			    // 	Insert putSP(_stack[_stack_depth-1].spm_addr)
			    CallInst::Create(func_putSP, ptr_spm_addr, "", nextInst);
			    // 	Insert a corresponding sload function
			    CallInst::Create(func_sload, "", nextInst);
			    // Check if the function has return value
			    Type * retty = funcCall->getType();
			    if (retty->isVoidTy())
				continue;
			    unsigned int i, n;
			    // Save the return value in a global variable temporarily until sload is executed if it is used
			    for (BasicBlock::iterator  ij = &*nextInst; ij != ie; ij++)
				for (i = 0, n = ij->getNumOperands(); i < n; i++)
				    if (ij->getOperand(i) == inst) { // We have found the use of the return value
					//if (caller->getName() == "smm_main" && callee->getName() == "f1")
					//errs() << caller->getName() << " calls " <<callee->getName() << " is managed!\n";
					GlobalVariable *gvar = NULL;
					// Always create a new global variable
					gvar = new GlobalVariable(mod, //Module
						retty, //Type
						false, //isConstant
						GlobalValue::ExternalLinkage, //linkage
						0, // Initializer
						"_gvar"); //Name
					// Initialize the temporary global variable
					gvar->setInitializer(Constant::getNullValue(retty));

					// Save the return value to the global variable before sload is called
					StoreInst *stRetVal = new StoreInst(funcCall, gvar);
					stRetVal->insertAfter(inst);
					// Read the global variable before the use of the return value, after sload is excuted
					LoadInst *ldGvarVal = new LoadInst(gvar, "", ij);
					// Replace the return value with the value of global variable
					ij->setOperand(i, ldGvarVal);
					break;
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

