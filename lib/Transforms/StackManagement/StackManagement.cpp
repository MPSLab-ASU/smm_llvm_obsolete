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
#include "llvm/IR/Module.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace
{
	struct StackManagerPass : public ModulePass
	{
		static char ID; // Pass identification, replacement for typeid
		StackManagerPass() : ModulePass(ID) {}

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

			// Global Variables
			GlobalVariable* gvar_spm_stack_base = mod.getGlobalVariable("_spm_stack_base");
			GlobalVariable* gvar_spm_depth = mod.getGlobalVariable("_stack_depth");
			GlobalVariable* gvar_stack = mod.getGlobalVariable("_stack");

			// Functions
			Function *func_g2l = mod.getFunction ("_g2l");
			Function *func_l2g = mod.getFunction ("_l2g");
			Function *func_sstore = mod.getFunction ("_sstore");
			Function *func_sload = mod.getFunction ("_sload");


			// Transform the program to use global variables to temporily save the return values - Jian
			for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
				for (Function::iterator bi = fi->begin(), be = fi->end(); bi != be; ++bi) {
					for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ii++) {
						Instruction *inst = ii;
						if (CallInst *funcCall = dyn_cast<CallInst>(inst)) {
							Function *callee = funcCall->getCalledFunction();
							if (callee == func_g2l || callee == func_l2g || callee == func_sstore && callee == func_sload)
								continue;
							Type * retty = funcCall->getType();
							if (retty->isVoidTy())
								continue;
							// We found a function call with return value
							GlobalVariable* gvar = mod.getOrInsertGlobal();
						}
					}
				}
			}


			// Insert management functions
			for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
				for (Function::iterator bi = fi->begin(), be = fi->end(); bi != be; ++bi) {
					for (BasicBlock::iterator ii = bi->begin(), in=++ii, ie = bi->end(); ii != ie; ii = in, in++) {
						Instruction *inst = ii;
						Instruction *nextInst = in;
						ii = inst;
						if (CallInst *funcCall = dyn_cast<CallInst>(inst)) {
							// We found a function call
							if (funcCall->getCalledFunction() != func_g2l && funcCall->getCalledFunction() != func_l2g &&
									funcCall->getCalledFunction() != func_sstore && funcCall->getCalledFunction() != func_sload) {
								// Insert a sstore function
								CallInst::Create (func_sstore, "", inst);
								// Insert putSP(_spm_stack_base)
								InlineAsm* func_putSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);
								CallInst::Create(func_putSP, gvar_spm_stack_base, "", inst);
								// read value of _stack_depth
								LoadInst* val__spm_depth = new LoadInst(gvar_spm_depth, "", false, nextInst);
								ConstantInt* const_int32_0 = ConstantInt::get(context, APInt(32, StringRef("0"), 10));
								ConstantInt* const_int64_1 = ConstantInt::get(context, APInt(64, StringRef("1"), 10));
								// calculate _stack_depth - 1
								BinaryOperator* val__spm_depth1 = BinaryOperator::Create(Instruction::Sub, val__spm_depth, const_int64_1, "sub", nextInst);
								// get the address of _stack[_stack_depth-1]
								std::vector<Value*> ptr_arrayidx_indices;
								ptr_arrayidx_indices.push_back(const_int32_0);
								ptr_arrayidx_indices.push_back(val__spm_depth1);
								Instruction* ptr_arrayidx = GetElementPtrInst::Create(gvar_stack, ptr_arrayidx_indices, "arrayidx", nextInst);
								// get the address of _stack[_stack_depth-1].spm_address
								std::vector<Value*> ptr_spm_addr_indices;
								ptr_spm_addr_indices.push_back(const_int32_0);
								ptr_spm_addr_indices.push_back(const_int32_0);
								Instruction* ptr_spm_addr = GetElementPtrInst::Create(ptr_arrayidx, ptr_spm_addr_indices, "spm_addr", nextInst);
								// Insert putSP(_stack[_stack_depth-1].spm_addr)
								CallInst::Create(func_putSP, ptr_spm_addr, "", nextInst);
								// Insert a corresponding sload function
								CallInst::Create (func_sload, "", nextInst);
							}
						}

					}
				}
			}

			// Transform the program so stack data addresses, if used as arguments, must be passed as pointers - Bryce
			for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
				for (Function::iterator bi = fi->begin(), be = fi->end(); bi != be; ++bi) {
					for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ii++) {
						if (CallInst *funcCall = dyn_cast<CallInst>(inst)) {	
							// Indentify function calls having stack data addresses as arguments
							for (unsigned int i = 0, n = inst->getNumArgOperands(); i < n; i++) {
								Value *operand = funcCall->getArgOperand(i);
								if (operand->getType()->isPointerTy() && isa<AllocaInst>operand) {
									// TODO: Create a pointer variable for each address and assign each pointer with a address correspondingly
									PointerType* PointerTy = PointerType::get(operand->getType(), 0);
									AllocaInst* ptr_p1 = new AllocaInst(PointerTy, "ptr", inst);
									errs() << *inst << "\n";
									// TODO: Replace all the use of each address with corresponding pointer
								}

							}
						}
					}
				}
			}


			// Insert l2g and g2l function
			for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
				for (Function::iterator bi = fi->begin(), be = fi->end(); bi != be; ++bi) {
					for (BasicBlock::iterator ii = bi->begin(), in=++ii, ie = bi->end(); ii != ie; ii = in, in++) {
						Instruction *inst = ii;
						Instruction *nextInst = in;
						ii = inst;

						// Identify definition of pointers to stack data
						if (inst->getOpcode() == Instruction::Store) {
							Value *operand0 = inst->getOperand(0);
							Value *operand1 = inst->getOperand(1);
							if (operand1->getType()->isPointerTy() && operand1->getType()->getPointerElementType()->isPointerTy() && !dyn_cast<Argument>(operand0) ) {
								//We have found a pointer to stack data on the LHS, we need to wrap the RHS in a l2g function call.  The RHS is not a function argument.
								IRBuilder<> builder(ii);
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
						// Identify deference of pointers to stack data
						else if (inst->getOpcode() == Instruction::Load) {
							Value *operand0 = inst->getOperand(0);
							if (operand0->getType()->isPointerTy() && operand0->getType()->getPointerElementType()->isPointerTy()) {
								if ( nextInst->getOpcode() == Instruction::Load && nextInst->getOperand(0) == inst) {
									// We have found a dereference of a pointer.  The next instruction is a load instruction and the current instructions value is the operand for the next instruction.
									errs() << fi->getName() << ":" << *inst << "\n";
									IRBuilder<> builder(nextInst);
									Value *castToCharStar = builder.CreatePointerCast(inst, Type::getInt8PtrTy(context), "castToChar*");
									Value *call_g2l = builder.CreateCall(func_g2l, castToCharStar, "call_g2l");
									Value *castFromCharStar = builder.CreatePointerCast(call_g2l, nextInst->getOperand(0)->getType(), "castFromChar*");
									nextInst->setOperand(0, castFromCharStar);
								} else if (nextInst->getOpcode() == Instruction::Store && nextInst->getOperand(1)->getValueID() == inst->getValueID()) {
									// We have found a dereference of a pointer.  The next instruction is a store instruction and the current instructions value is the operand for the next instruction.
									errs() << fi->getName() << ":" << *inst << "\n";
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

			return true;
		}
	};
}

char StackManagerPass::ID = 0; //Id the pass.
static RegisterPass<StackManagerPass> X("smm-stack", "Stack Management Pass"); //Register the pass.

