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

#define DEBUG_TYPE "smmcm"

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
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
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/YAMLTraits.h"

#include <fstream>
#include <iostream>
#include <string>
#include <vector>

#include "FuncType.h"


using namespace llvm;

namespace {
    struct CodeManagement : public ModulePass { // Insert code management functions
	static char ID; // Pass identification, replacement for typeid
	CodeManagement() : ModulePass(ID) {}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	// Build the wrapper function: retTy c_call(char *callerName, char *calleeName, calleeTy calleeAddr, ...)
	Function *build_c_call(CallInst *call_inst)
	{
	    // Get the caller
	    Function* caller = call_inst->getParent()->getParent();
	    // Get the called function
	    Function* callee = call_inst->getCalledFunction();
	    Module *mod = caller->getParent();
	    LLVMContext &context = mod->getContext();
	    IRBuilder <> builder(context);

	    FunctionType* calleeTy = NULL;
	    Type *retTy = NULL;
	    std::vector<Type*>calleeArgTy;
	    // Get the type of the called function
	    calleeTy = callee->getFunctionType();
	    // Get arguments types of the called function (if there are any)
	    for (unsigned int i = 0, num = call_inst->getNumArgOperands(); i < num; i++) {
		calleeArgTy.push_back(call_inst->getArgOperand(i)->getType());
	    }
	    // Get the return type of the called function
	    retTy = callee->getReturnType();

	    // Create a pointer type to char
	    PointerType *ptrTy_int8 = PointerType::get(IntegerType::get(context, 8), 0);
	    // Create a pointer type to callee type
	    PointerType *calleeTyPtr = PointerType::get(calleeTy, 0);
	    // Get the pointer to c_get function
	    Function* func_c_get = mod->getFunction("c_get");
	    assert(func_c_get);

	    Function* func_c_call =  nullptr;
	    
	    // Go through all the exsiting wrapper functions and check if there is any one can be used directly
	    for (Module::iterator fi = mod->begin(), fe = mod->end(); fi != fe; ++fi) {
		if (fi->getName().count("c_call") == 1) {
		    //int num_args_before = 2;
		    int num_args_before = 3;
		    FunctionType *fiTy = fi->getFunctionType();
		    // Compare the return types
		    FunctionType *fiCalleeTy = (FunctionType *)(((PointerType *)fiTy->getParamType(num_args_before-1))->getElementType());
		    //errs() << *fiCalleeTy->getReturnType() <<"\n";
		    Type *fiCalleeRetTy = fiCalleeTy->getReturnType();
		    if (retTy != fiCalleeRetTy ) {
			continue;
		    }

		    // Compare number of arguments
		    unsigned int fiNumCalleeParams = fiTy->getNumParams() - num_args_before;
		    if(calleeArgTy.size() != fiNumCalleeParams)
			continue;
		    // Compare argument types 
		    unsigned int i = num_args_before;
		    std::vector<Type*>::iterator ai = calleeArgTy.begin(), ae = calleeArgTy.end();
		    while( ai!=ae) {
			if(*ai != fiTy->getParamType(i)) 
			    break;
			ai++;
			i++;
		    }
		    if (ai!=ae)
			continue;
		    // If all the above tests pass, then return the wrapper function
		    func_c_call = fi;
		    return func_c_call;
		}
	    }

	    // Create a function type for c_call it has not been created for corresponding function type
	    if (!func_c_call) {
		std::vector<Type*> c_call_params;
		// The first parameter should be a char pointer to caller name
		c_call_params.push_back(ptrTy_int8);
		// The second parameter should be a char pointer to callee name
		c_call_params.push_back(ptrTy_int8);
		// The third parameter should be a callee function type pointer to callee address
		c_call_params.push_back(calleeTyPtr);
		// The following parameters should be the callee arguments if passed in
		for (std::vector<Type*>::iterator ai = calleeArgTy.begin(), ae = calleeArgTy.end(); ai!=ae; ++ai)
		    c_call_params.push_back(*ai);
		FunctionType* funcTy = FunctionType::get(
			retTy,
			c_call_params,
			false);

		func_c_call = Function::Create(
			funcTy,
			GlobalValue::LinkOnceODRLinkage ,
			"c_call", mod);
		
		errs() << *ptrTy_int8 << "\n";
		errs() << *calleeTyPtr << "\n";
	    }

	    assert(func_c_call);

	    // Get arguments for c_call
	    Function::arg_iterator ai = func_c_call->arg_begin();
	    // Get caller address from first argument
	    Value* caller_name = ai++;
	    caller_name->setName("callername");
	    // Get callee address from second argument
	    Value* callee_name = ai++;
	    callee_name->setName("calleename");
	    // Skip callee type from the third argument 
	    //Value* callee = ai++;
	    //callee->setName("callee");
	    ai++;
	    // Get addresses of callee arguments from following arguments if passed in
	    std::vector<Value*>callee_arg;
	    for (Function::arg_iterator ae = func_c_call->arg_end(); ai!=ae; ai++) {
		static int i = 0;
		Value* arg = ai;
		arg->setName("arg" + std::to_string(i++));
		callee_arg.push_back(arg);
	    }

	    // Block entry (c_call_entry)
	    BasicBlock* c_call_entry = BasicBlock::Create(context, "entry",func_c_call, 0);
	    builder.SetInsertPoint(c_call_entry);

	    // Create local variables for callee arugments if passed in
	    std::vector<AllocaInst*> callee_arg_addr;
	    for (std::vector<Type*>::size_type i = 0; i < calleeArgTy.size(); i++) {	
		AllocaInst* arg_addr = builder.CreateAlloca(calleeArgTy[i], nullptr, "callee_arg" + std::to_string(i));
		callee_arg_addr.push_back(arg_addr);
	    }

	    // Allocate space for return value if its type is not void
	    AllocaInst* ret_val;
	    if (!retTy->isVoidTy()) {
		ret_val = builder.CreateAlloca(retTy, nullptr, "ret_val");
	    }
	    
	    // Copy the callee arguments to the local variables if passed in
	    for (std::vector<Value*>::size_type i = 0; i < callee_arg.size(); i++) {
		builder.CreateStore(callee_arg[i], callee_arg_addr[i], false);
	    }

	    // Find out the SPM address for callee
	   CallInst* callee_vma_int8 = CallInst::Create(func_c_get, callee_name, "callee_vma_int8", c_call_entry);
	   // Cast the type of the SPM address to the function type of the callee
	    CastInst* callee_vma = cast <CastInst> (builder.CreateBitCast(callee_vma_int8, calleeTyPtr)); 

	    // Read callee arguments and get their values if passed in
	    std::vector<Value*>callee_arg_vals;
	    for (std::vector<AllocaInst*>::iterator ai = callee_arg_addr.begin(), ae = callee_arg_addr.end(); ai != ae; ai++) {
		LoadInst* arg_val = builder.CreateLoad(*ai);
		callee_arg_vals.push_back(arg_val);
	    }

	    // Call the callee
	    //CallInst* int32_call1 = CallInst::Create(callee_vma, callee_arg_vals, "", c_call_entry);
	    CallInst* int32_call1 = builder.CreateCall(callee_vma, callee_arg_vals, "callee_vma");

	    // Get return value if its type is not void
	    if (!retTy->isVoidTy()) {
		builder.CreateStore(int32_call1, ret_val, false);
	    } 

	    // Ensure the caller is present after the callee returns
	    CallInst::Create(func_c_get, caller_name, "caller_vma", c_call_entry);


	    // Read return value and return it if its type is not void
	    LoadInst *int32_632;
	    if (!retTy->isVoidTy()) {
		int32_632 = builder.CreateLoad(ret_val);
		ReturnInst::Create(context, int32_632, c_call_entry);
	    } else {
		ReturnInst::Create(context, c_call_entry);
	    }
	    return func_c_call;
	}


	virtual bool runOnModule (Module &mod) {
	    LLVMContext &context = mod.getContext();
	    IRBuilder<> builder(context); // Instruction will be inserted before this instruction 
	    //PointerType *ptrTy_int8 = PointerType::get(IntegerType::get(context, 8), 0);
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph(); // call graph

	    Function *func_main = mod.getFunction("main");
	    assert(func_main);
	    // Check the potential callers
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		if(CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second)) {
		    Function *fi = cgn->getFunction();
		    // Skip external nodes
		    if(!fi)
			continue;
		    // Skip library functions
		    if (isLibraryFunction(fi))
			continue;
		    // Skip code management functions
		    if (isCodeManagementFunction(fi))
			continue;
		    // Skip the main function
		    if (fi == func_main)
			continue;

		    // User-defined caller functions
		    DEBUG(errs() << fi->getName() <<"\n");
		    for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
			CallInst *call_inst = dyn_cast <CallInst> (cgni->first);
			BasicBlock::iterator ii(call_inst);
			CallGraphNode *called_cgn = dyn_cast <CallGraphNode> (cgni->second);
			Function *callee = called_cgn->getFunction();
			assert(call_inst && called_cgn);

			builder.SetInsertPoint(call_inst);
			// Skip inline assembly
			if (call_inst->isInlineAsm())
			    continue;
			// Skip calls to function pointers
			if (!callee) 
			    continue;
			// Skip calls to management functions
			if(isCodeManagementFunction(callee))
			    continue;
			// Skip recursive edges
			//if (cgn == called_cgn) 
			//continue;

			// If the caller calls an user-defined function
			if (!isLibraryFunction(callee)) { 
			    DEBUG(errs() << "\tcalls " << callee->getName() <<" (U)\n");
			    //FunctionType* calleeTy = NULL;
			    std::vector<Type*>calleeArgTy;
			    // Get a pointer to the callee function type
			    //calleeTy = callee->getFunctionType();
			    // Get callee argument types if there are any
			    for (unsigned int i = 0, num = call_inst->getNumArgOperands(); i < num; i++) {
				calleeArgTy.push_back(call_inst->getArgOperand(i)->getType());
			    }
			    // Create a wrapper function for callee
			    //Function *func_c_call = build_c_call(&mod, calleeTy, callee->getReturnType(), calleeArgTy);
			    Function *func_c_call = build_c_call(call_inst);
			    /*
			    // Create a function pointer with the same type of the wrapper function to enforce absolute call
			    PointerType* FuncTyPtr = PointerType::get(func_c_call->getFunctionType(), 0);
			    AllocaInst* funcPtr = builder.CreateAlloca(FuncTyPtr, nullptr, "c_call_abs");
			    // Copy the wrapper function address to the function pointer
			    builder.CreateStore(func_c_call, funcPtr, false);
			    // Read the value of the function pointer
			    LoadInst* ldFuncPtr = builder.CreateLoad(funcPtr);
			    */
			    // Pass arguments to the pointer to the wraper function
			    std::vector<Value*> call_args;

			    Value *caller_name_ptr = builder.CreateGlobalStringPtr(fi->getName(), "caller.name");
			    Value *callee_name_ptr = builder.CreateGlobalStringPtr(callee->getName(), "callee.name");
			    // Pass caller address with char* type as the first argument
			    //Constant* int8_caller = ConstantExpr::getCast(Instruction::BitCast, fi, ptrTy_int8);
			    //call_args.push_back(int8_caller);
			    call_args.push_back(caller_name_ptr);
			    // Pass callee name as the second argument
			    call_args.push_back(callee_name_ptr);
			    // Pass callee address as the third argument
			    call_args.push_back(callee);
			    // Pass callee arguments if there are any as the following arguments
			    for (unsigned int i = 0, num = call_inst->getNumArgOperands(); i < num; i++) {
				call_args.push_back(call_inst->getArgOperand(i));
			    }
			    // Create a new call instruction to the wrapper function
			    //CallInst* call_c_call = CallInst::Create(ldFuncPtr, call_args);
			    CallInst* call_c_call = CallInst::Create(func_c_call, call_args);
			    // Replace all the uses of the original call instruction with the new call instruction
			    ReplaceInstWithInst(call_inst->getParent()->getInstList(), ii, call_c_call);
			}
			/*
			else if (!callee->isIntrinsic()) {  // If the caller calls an librarfy function 
			    DEBUG(errs() << "\tcalls " << callee->getName() <<" (L)\n");
			    // Create a function pointer with the same type of callee to enforce absolute call
			    PointerType* FuncTyPtr = PointerType::get(callee->getFunctionType(), 0);
			    AllocaInst* funcPtr = builder.CreateAlloca(FuncTyPtr, nullptr, callee->getName() + "_ptr");
			    // Copy the callee address to the function pointer
			    builder.CreateStore(callee, funcPtr, false);
			    // Read the value of the function pointer
			    LoadInst* ldFuncPtr = builder.CreateLoad(funcPtr); 

			    // Pass arguments of the callee to the function pointer if there are any
			    std::vector<Value*> call_args;
			    for (unsigned int i = 0, num = call_inst->getNumArgOperands(); i < num; i++) {
				call_args.push_back(call_inst->getArgOperand(i));
			    }
			    // Create a new call instruction with the function pointer
			    CallInst* callFuncPtr = CallInst::Create(ldFuncPtr, call_args);
			    // Replace all the uses of the original call instruction with the new call instruction
			    ReplaceInstWithInst(call_inst->getParent()->getInstList(), ii, callFuncPtr);
			} else { // If the caller calls an intrinsic function
			    StringRef callee_libc_name = callee->getName().split('.').second.split('.').first;
			    DEBUG(errs() << "\tcalls " << callee_libc_name <<" (I)\n");
			    if (callee_libc_name.startswith("mem")) {
				Function *callee_libc = mod.getFunction(callee_libc_name);
				if (!callee_libc) {
				    if (callee_libc_name == "memcpy") {
					std::vector<Type*>FuncTy_args;
					FuncTy_args.push_back(ptrTy_int8);
					FuncTy_args.push_back(ptrTy_int8);
					FuncTy_args.push_back(IntegerType::get(context, 64));
					FunctionType* FuncTy = FunctionType::get(
						ptrTy_int8,
						FuncTy_args,
						false);

					callee_libc = Function::Create(
						FuncTy,
						GlobalValue::ExternalLinkage,
						"memcpy", &mod); 
					callee_libc->setCallingConv(CallingConv::C);
				    }
				    else if (callee_libc_name == "memset") {
					std::vector<Type*>FuncTy_args;
					FuncTy_args.push_back(ptrTy_int8);
					FuncTy_args.push_back(IntegerType::get(context, 32));
					FuncTy_args.push_back(IntegerType::get(context, 64));
					FunctionType* FuncTy = FunctionType::get(
						ptrTy_int8,
						FuncTy_args,
						false);

					callee_libc = Function::Create(
						FuncTy,
						GlobalValue::ExternalLinkage,
						"memset", &mod); 
					callee_libc->setCallingConv(CallingConv::C);
				    }
				}
				assert(callee_libc);

				// Create a function pointer with the same type of callee to enforce absolute call
				PointerType* FuncTyPtr = PointerType::get(callee_libc->getFunctionType(), 0);

				//AllocaInst* funcPtr = new AllocaInst(FuncTyPtr, callee_libc->getName() + "_ptr", inst);
				//funcPtr->setAlignment(8);
				AllocaInst* funcPtr = builder.CreateAlloca(FuncTyPtr, nullptr, callee_libc->getName() + "_ptr");
				// Copy the callee address to the function pointer
				//StoreInst* stFuncPtr = new StoreInst(callee_libc, funcPtr, false, inst);
				//stFuncPtr->setAlignment(8); 
				builder.CreateStore(callee_libc, funcPtr);
				// Read the value of the function pointer
				//LoadInst* ldFuncPtr = new LoadInst(funcPtr, "", false, inst);
				//ldFuncPtr->setAlignment(8); 
				LoadInst* ldFuncPtr = builder.CreateLoad(funcPtr);
				// Pass arguments of the callee to the function pointer if there are any
				std::vector<Value*> call_args;
				for (unsigned int i = 0, num = callee_libc->getFunctionType()->getNumParams(); i < num; i++) {
				    //errs() << callee_libc->getFunctionType()->getParamType(i) << " " << inst->getArgOperand(i) <<"\n";
				    call_args.push_back(call_inst->getArgOperand(i));
				}
				//CallInst* callFuncPtr = CallInst::Create(ldFuncPtr, call_args);
				//ReplaceInstWithInst(ii->getParent()->getInstList(), ii, callFuncPtr);
				// Create a new call instruction with the function pointer
				//CallInst* callFuncPtr = CallInst::Create(ldFuncPtr, call_args, "", call_inst);
				builder.CreateCall(ldFuncPtr, call_args, "");
				// Move iterator one instruction back so its value will not be nullified. After this step the iterator is guaranteed to be valid, since we have inserted instructions before
				ii--;
				// Remove the original call instruction since llvm.memcpy has a void return type
				call_inst->eraseFromParent();
			    }
			}
		*/
		    }
		}
	    }

	    return true;
	}

    };
}

char CodeManagement::ID = 0;
static RegisterPass<CodeManagement> X("smmcm", "Code management Pass)");
