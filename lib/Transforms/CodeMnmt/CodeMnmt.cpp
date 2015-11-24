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

#define DEBUG_TYPE "smm"

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/YAMLTraits.h"

#include <fstream>
#include <iostream>
#include <string>
#include <vector>


using namespace llvm;

namespace {
	struct CodeManagement : public ModulePass { // Insert code management functions
		static char ID; // Pass identification, replacement for typeid
		CodeManagement() : ModulePass(ID) {}

		// Checks whether a function is defined by users in C programs
		inline bool isUserDefined(Function *func) {
			if ((!func->getName().startswith("_Z") || !yaml::isNumber(func->getName().substr(2,1))))
				return false;
			// main function should have been redefined as a user function
			//if (!func->getName().startswith("_Z") || !yaml::isNumber(func->getName().substr(2,1)))
			//return false;
			return true;
		}
		inline bool isMnmFunc(Function *func)
		{
			if (func->getName().count("c_get") ==1)
				return true;
			if (func->getName().count("c_call") ==1)
				return true;
			if (func->getName().count("c_init") ==1)
				return true;
			return false;
		}

		// Build the wrapper function: retTy c_call(char *callerAddr, calleeTy calleeAddr, ...)
		Function *build_c_call(Module *mod, FunctionType *calleeTy, Type *retTy, std::vector<Type*>calleeArgTy)
		{
			LLVMContext &context = mod->getContext();
			// Create a pointer type to char
			PointerType *PointerTy_1 = PointerType::get(IntegerType::get(context, 8), 0);
			// Create a pointer type to callee type
			PointerType *calleeTyPtr = PointerType::get(calleeTy, 0);
			// Get the pointer to c_get function
			Function* func_c_get = mod->getFunction("_Z5c_getPc");
			assert(func_c_get);

			Function* func_c_call =  NULL;
			// Go through all the exsiting wrapper functions and check if there is any one can be used directly
			for (Module::iterator fi = mod->begin(), fe = mod->end(); fi != fe; ++fi) {
				if (fi->getName().count("c_call") == 1) {
					FunctionType *fiTy = fi->getFunctionType();
					// Compare the return types
					FunctionType *fiCalleeTy = (FunctionType *)(((PointerType *)fiTy->getParamType(1))->getElementType());
					//errs() << *fiCalleeTy->getReturnType() <<"\n";
					Type *fiCalleeRetTy = fiCalleeTy->getReturnType();
					if (retTy != fiCalleeRetTy ) {
						continue;
					}

					// Compare number of arguments
					unsigned int fiNumCalleeParams = fiTy->getNumParams() - 2;
					if(calleeArgTy.size() != fiNumCalleeParams)
						continue;
					// Compare argument types 
					unsigned int i = 2;
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
				std::vector<Type*>c_call_params;
				// The first parameter should be of a char pointer to caller address
				c_call_params.push_back(PointerTy_1);
				// The second parameter should be a callee function type pointer to callee address
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
						"_Z6c_call", mod);
				func_c_call->setCallingConv(CallingConv::C);
				AttributeSet func_c_call_PAL;
				SmallVector<AttributeSet, 4> Attrs;
				AttributeSet PAS;
				AttrBuilder B;
				B.addAttribute(Attribute::UWTable);
				PAS = AttributeSet::get(context, ~0U, B);
				Attrs.push_back(PAS);
				func_c_call_PAL = AttributeSet::get(context, Attrs);
				func_c_call->setAttributes(func_c_call_PAL);
			}

			assert(func_c_call);

			// Get arguments for c_call
			Function::arg_iterator ai = func_c_call->arg_begin();
			// Get caller address from first argument
			Value* ptr_caller = ai++;
			ptr_caller->setName("caller");
			// Get callee address from second argument
			Value* ptr_callee = ai++;
			ptr_callee->setName("callee");
			// Get addresses of callee arguments from following arguments if passed in
			std::vector<Value*>ptr_callee_arg;
			for (Function::arg_iterator ae = func_c_call->arg_end(); ai!=ae; ai++) {
				static int i = 0;
				Value* arg = ai;
				arg->setName("arg" + std::to_string(i++));
				ptr_callee_arg.push_back(arg);
			}

			BasicBlock* label_entry_597 = BasicBlock::Create(context, "entry",func_c_call, 0);

			// Block entry (label_entry_597)

			// Create a local variable for caller address
			AllocaInst* ptr_caller_addr = new AllocaInst(PointerTy_1, "caller.addr", label_entry_597);
			ptr_caller_addr->setAlignment(8);
			// Create a local variable for callee address
			AllocaInst* ptr_callee_addr = new AllocaInst(calleeTyPtr, "callee.addr", label_entry_597);
			ptr_callee_addr->setAlignment(8);

			// Create local variables for callee arugments if passed in
			std::vector<AllocaInst*> ptr_callee_arg_addr;
			for (std::vector<Type*>::size_type i = 0; i < calleeArgTy.size(); i++) {	
				AllocaInst* arg_addr = new AllocaInst(calleeArgTy[i], "callee_arg" + std::to_string(i) + ".addr", label_entry_597);
				ptr_callee_arg_addr.push_back(arg_addr);
			}

			// Create a pointer to callee function type
			AllocaInst* ptr_callee_spm = new AllocaInst(calleeTyPtr, "callee_spm", label_entry_597);
			ptr_callee_spm->setAlignment(8);
			AllocaInst* ptr_ret_val;
			// Allocate space for return value if its type is not void
			if (!retTy->isVoidTy()) {
				ptr_ret_val = new AllocaInst(retTy, "ret_val", label_entry_597);
				ptr_ret_val->setAlignment(4);
			}
			// Copy the caller address to the local variable, both should be of char pointer type
			StoreInst* void_598 = new StoreInst(ptr_caller, ptr_caller_addr, false, label_entry_597);
			void_598->setAlignment(8);
			// Copy the callee address to the local variable
			StoreInst* void_602 = new StoreInst(ptr_callee, ptr_callee_addr, false, label_entry_597);
			void_602->setAlignment(8);

			// Copy the callee arguments to the local variables if passed in
			for (std::vector<Value*>::size_type i = 0; i < ptr_callee_arg.size(); i++) {
				StoreInst *stInst = new StoreInst(ptr_callee_arg[i], ptr_callee_arg_addr[i], false, label_entry_597);
				stInst->setAlignment(4);
			}

			// Find out the SPM address for callee
			LoadInst* ptr_617 = new LoadInst(ptr_callee_addr, "", false, label_entry_597);
			ptr_617->setAlignment(8);
			CastInst* ptr_618 = new BitCastInst(ptr_617, PointerTy_1, "", label_entry_597);
			CallInst* ptr_call_619 = CallInst::Create(func_c_get, ptr_618, "call", label_entry_597);
			ptr_call_619->setCallingConv(CallingConv::C);
			ptr_call_619->setTailCall(false);
			AttributeSet ptr_call_619_PAL;
			ptr_call_619->setAttributes(ptr_call_619_PAL);
			// Copy the SPM address to the pointer to callee function type
			CastInst* ptr_620 = new BitCastInst(ptr_call_619, calleeTyPtr, "", label_entry_597);
			StoreInst* void_621 = new StoreInst(ptr_620, ptr_callee_spm, false, label_entry_597);
			void_621->setAlignment(8);
			LoadInst* ptr_625 = new LoadInst(ptr_callee_spm, "", false, label_entry_597);
			ptr_625->setAlignment(8);

			// Read callee arguments and get their values if passed in
			std::vector<Value*>callee_arg_vals;
			for (std::vector<AllocaInst*>::iterator ai = ptr_callee_arg_addr.begin(), ae = ptr_callee_arg_addr.end(); ai != ae; ai++) {
				LoadInst* arg_val = new LoadInst(*ai, "", false, label_entry_597);
				callee_arg_vals.push_back(arg_val);
			}

			// Call the pointer
			CallInst* int32_call1;
			//int32_call1 = CallInst::Create(ptr_625, callee_arg_vals, "call1", label_entry_597);
			int32_call1 = CallInst::Create(ptr_625, callee_arg_vals, "", label_entry_597);

			int32_call1->setCallingConv(CallingConv::C);
			int32_call1->setTailCall(false);
			AttributeSet int32_call1_PAL;
			int32_call1->setAttributes(int32_call1_PAL);

			// Get return value if its type is not void
			StoreInst *void_628;
			if (!retTy->isVoidTy()) {
				void_628 = new StoreInst(int32_call1, ptr_ret_val, false, label_entry_597);
				void_628->setAlignment(4);
			} 

			// Ensure caller is present
			LoadInst* ptr_629 = new LoadInst(ptr_caller_addr, "", false, label_entry_597);
			ptr_629->setAlignment(8);
			CastInst* ptr_630 = new BitCastInst(ptr_629, PointerTy_1, "", label_entry_597);
			CallInst* ptr_call2_631 = CallInst::Create(func_c_get, ptr_630, "call2", label_entry_597);
			ptr_call2_631->setCallingConv(CallingConv::C);
			ptr_call2_631->setTailCall(false);
			AttributeSet ptr_call2_631_PAL;
			ptr_call2_631->setAttributes(ptr_call2_631_PAL);


			// Read return value and return it if its type is not void
			LoadInst *int32_632;
			if (!retTy->isVoidTy()) {
				int32_632 = new LoadInst(ptr_ret_val, "", false, label_entry_597);
				int32_632->setAlignment(4);
				ReturnInst::Create(context, int32_632, label_entry_597);
			} else {
				ReturnInst::Create(context, label_entry_597);
			}
			//return 0;
			return func_c_call;
		}


		virtual bool runOnModule (Module &mod) {
			LLVMContext &context = mod.getContext();
			PointerType *PointerTy_1 = PointerType::get(IntegerType::get(context, 8), 0);
			// Check the potential callers
			for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
				// Skip non-user-defined functions
				if (!isUserDefined(fi))
					continue;
				// Skip code management functions
				if (isMnmFunc(fi))
					continue;
				// User-defined caller functions
				errs() << fi->getName() <<"\n";
				// Check the potential callees
				for (Function::iterator bi = fi->begin(), be = fi->end(); bi != be; ++bi) 
					for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ++ii) {
						if (CallInst *inst = dyn_cast<CallInst>(&*ii)) {
							Function *callee = inst->getCalledFunction();
							// Skip calls to function pointers
							if (!callee) 
								continue;
							// Skip code management functions
							if (isMnmFunc(callee))
								continue;

							// If the caller calls a user-defined function
							if (isUserDefined(callee)) { 
								errs() << "\tcalls " << callee->getName() <<" (U)\n";
								FunctionType* calleeTy = NULL;
								std::vector<Type*>calleeArgTy;
								// Get a pointer to the callee function type
								calleeTy = callee->getFunctionType();
								// Get callee argument types if there are any
								for (unsigned int i = 0, num = inst->getNumArgOperands(); i < num; i++) {
									calleeArgTy.push_back(inst->getArgOperand(i)->getType());
								}
								// Create a wrapper function for callee
								Function *func_c_call = build_c_call(&mod, calleeTy, callee->getReturnType(), calleeArgTy);
								// Create a function pointer with the same type of the wrapper function to enforce absolute call
								PointerType* FuncTyPtr = PointerType::get(func_c_call->getFunctionType(), 0);
								AllocaInst* funcPtr = new AllocaInst(FuncTyPtr, "c_call_abs", inst);
								funcPtr->setAlignment(8);
								// Copy the wrapper function address to the function pointer
								StoreInst* stFuncPtr = new StoreInst(func_c_call, funcPtr, false, inst);
								stFuncPtr->setAlignment(8); 
								// Read the value of the function pointer
								LoadInst* ldFuncPtr = new LoadInst(funcPtr, "", false, inst);
								ldFuncPtr->setAlignment(8); 
								// Pass arguments to the pointer to the wraper function
								std::vector<Value*> call_args;
								// Pass caller address with char* type as the first argument
								Constant* int8_caller = ConstantExpr::getCast(Instruction::BitCast, fi, PointerTy_1);
								call_args.push_back(int8_caller);
								// Pass callee address as the second argument
								call_args.push_back(callee);
								// Pass callee arguments if there are any as the following arguments
								for (unsigned int i = 0, num = inst->getNumArgOperands(); i < num; i++) {
									call_args.push_back(inst->getArgOperand(i));
								}
								// Create a new call instruction to the wrapper function
								CallInst* call_c_call = CallInst::Create(ldFuncPtr, call_args);
								// Replace all the uses of the original call instruction with the new call instruction
								ReplaceInstWithInst(ii->getParent()->getInstList(), ii, call_c_call);
							} else  if (!callee->isIntrinsic()) {  // If the caller calls an librarfy function 
								errs() << "\tcalls " << callee->getName() <<" (L)\n";
								// Create a function pointer with the same type of callee to enforce absolute call
								PointerType* FuncTyPtr = PointerType::get(callee->getFunctionType(), 0);
								AllocaInst* funcPtr = new AllocaInst(FuncTyPtr, callee->getName() + "_ptr", inst);
								//AllocaInst* funcPtr = new AllocaInst(FuncTyPtr, callee->getName() + "_ptr", bi->begin());
								funcPtr->setAlignment(8);
								// Copy the callee address to the function pointer
								StoreInst* stFuncPtr = new StoreInst(callee, funcPtr, false, inst);
								stFuncPtr->setAlignment(8); 
								// Read the value of the function pointer
								LoadInst* ldFuncPtr = new LoadInst(funcPtr, "", false, inst);
								ldFuncPtr->setAlignment(8); 
								// Pass arguments of the callee to the function pointer if there are any
								std::vector<Value*> call_args;
								for (unsigned int i = 0, num = inst->getNumArgOperands(); i < num; i++) {
									call_args.push_back(inst->getArgOperand(i));
								}
								// Create a new call instruction with the function pointer
								CallInst* callFuncPtr = CallInst::Create(ldFuncPtr, call_args);
								// Replace all the uses of the original call instruction with the new call instruction
								ReplaceInstWithInst(ii->getParent()->getInstList(), ii, callFuncPtr);
							} else { // If the caller calls an intrinsic function
								StringRef callee_libc_name = callee->getName().split('.').second.split('.').first;
								errs() << "\tcalls " << callee_libc_name <<" (I)\n";
								if (callee_libc_name.startswith("mem")) {
									Function *callee_libc = mod.getFunction(callee_libc_name);
									if (!callee_libc) {
										if (callee_libc_name == "memcpy") {
											std::vector<Type*>FuncTy_args;
											FuncTy_args.push_back(PointerTy_1);
											FuncTy_args.push_back(PointerTy_1);
											FuncTy_args.push_back(IntegerType::get(context, 64));
											FunctionType* FuncTy = FunctionType::get(
													PointerTy_1,
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
											FuncTy_args.push_back(PointerTy_1);
											FuncTy_args.push_back(IntegerType::get(context, 32));
											FuncTy_args.push_back(IntegerType::get(context, 64));
											FunctionType* FuncTy = FunctionType::get(
													PointerTy_1,
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
									//AllocaInst* funcPtr = new AllocaInst(FuncTyPtr, "func_ptr", inst);
									AllocaInst* funcPtr = new AllocaInst(FuncTyPtr, callee_libc->getName() + "_ptr", inst);
									funcPtr->setAlignment(8);
									// Copy the callee address to the function pointer
									StoreInst* stFuncPtr = new StoreInst(callee_libc, funcPtr, false, inst);
									stFuncPtr->setAlignment(8); 
									// Read the value of the function pointer
									LoadInst* ldFuncPtr = new LoadInst(funcPtr, "", false, inst);
									ldFuncPtr->setAlignment(8); 
									// Pass arguments of the callee to the function pointer if there are any
									std::vector<Value*> call_args;
									for (unsigned int i = 0, num = callee_libc->getFunctionType()->getNumParams(); i < num; i++) {
										//errs() << callee_libc->getFunctionType()->getParamType(i) << " " << inst->getArgOperand(i) <<"\n";
										call_args.push_back(inst->getArgOperand(i));
									}
									//CallInst* callFuncPtr = CallInst::Create(ldFuncPtr, call_args);
									//ReplaceInstWithInst(ii->getParent()->getInstList(), ii, callFuncPtr);
									// Create a new call instruction with the function pointer
									CallInst* callFuncPtr = CallInst::Create(ldFuncPtr, call_args, "", inst);
									// Move iterator one instruction back so its value will not be nullified. After this step the iterator is guaranteed to be valid, since we have inserted instructions before
									ii--;
									// Remove the original call instruction since llvm.memcpy has a void return type
									inst->eraseFromParent();
								}
							}
						}
					}
			}

			return true;
		}

	};
}

char CodeManagement::ID = 0;
static RegisterPass<CodeManagement> X("smmcm", "Code management Pass)");
