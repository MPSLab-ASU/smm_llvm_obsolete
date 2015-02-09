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
        
        virtual bool runOnModule(Module &M)
        {
            Function *g2l_function = cast<Function>(M.getOrInsertFunction ("__g2l", Type::getInt8PtrTy(getGlobalContext()), Type::getInt8PtrTy(getGlobalContext()), NULL));
            Function *l2g_function = cast<Function>(M.getOrInsertFunction ("__l2g", Type::getInt8PtrTy(getGlobalContext()), Type::getInt8PtrTy(getGlobalContext()), NULL));
            Function *sstore_function = cast<Function>(M.getOrInsertFunction ("__sstore", Type::getVoidTy(getGlobalContext()), NULL));
            Function *sload_function = cast<Function>(M.getOrInsertFunction ("__sload", Type::getVoidTy(getGlobalContext()), NULL));
            
            // Get all functions in a module
            for (Module::iterator mItr = M.begin(); mItr != M.end(); ++mItr)
            {
                // Get all basic blocks in a function
                for (Function::iterator fItr = mItr->begin(); fItr != mItr->end(); ++fItr)
                {
                    // Get all instructions in a basic block
                    for (BasicBlock::iterator bItr = fItr->begin(); bItr != fItr->end(); ++bItr)
                    {
                        Instruction *inst = bItr;
                        Instruction *nextInst = ++bItr;
                        bItr = inst;
                        
                        if (CallInst *functionCall = dyn_cast<CallInst>(inst))
                        {
                            if (functionCall->getCalledFunction() != g2l_function && functionCall->getCalledFunction() != l2g_function &&
                                functionCall->getCalledFunction() != sstore_function && functionCall->getCalledFunction() != sload_function)
                            {
                                CallInst::Create (sstore_function, "", functionCall);
                                CallInst::Create (sload_function, "", nextInst);
                            }
                        }
                        
                        // Get all operands in an instruction
                        for (unsigned int iIndex = 0; iIndex < inst->getNumOperands(); ++iIndex)
                        {
                            Value *operand = inst->getOperand(iIndex);
                            
                            // If we find a pointer operand and it is a pointer to a pointer, then in LLVM IR it can be a pointer to stack data.
                            if (operand->getType()->isPointerTy() && operand->getType()->getPointerElementType()->isPointerTy())
                            {
                                if ( iIndex == 1 && !dyn_cast<Argument>( inst->getOperand(0) ) )
                                {
                                    //We have found a pointer to stack data on the LHS, we need to wrap the RHS in a l2g function call.  The RHS is not a function argument.
                                    IRBuilder<> builder(bItr);
                                    // Take the data on the RHS and cast it to void * so it can be passed ot our function l2g
                                    Value *castToVoidStar = builder.CreatePointerCast(inst->getOperand(0), Type::getInt8PtrTy(getGlobalContext()), "castToVoid*");
                                    // Call the function l2g and pass the void * data as a parameter to the function
                                    Value *call_l2g = builder.CreateCall(l2g_function, castToVoidStar, "call__l2g");
                                    // Take the result from the function call and cast it to its previous type.
                                    Value *castFromVoidStar = builder.CreatePointerCast(call_l2g, inst->getOperand(0)->getType(), "castFromVoid*");
                                    // Assign the result to the LHS of the original instruction.
                                    builder.CreateStore(castFromVoidStar, operand);
                                    // Delete the original instruction.
                                    (bItr++)->eraseFromParent();
                                }
                                else if (nextInst->getOpcode() == Instruction::Load && nextInst->getOperand(0)->getValueID() == inst->getValueID())
                                {
                                    // We have found a dereference of a pointer.  The next instruction is a load instruction and the current instructions value is the operand for the next instruction.
                                    IRBuilder<> builder(nextInst);
                                    Value *castToVoidStar = builder.CreatePointerCast(inst, Type::getInt8PtrTy(getGlobalContext()), "castToVoid*");
                                    Value *call_g2l = builder.CreateCall(g2l_function, castToVoidStar, "call__g2l");
                                    Value *castFromVoidStar = builder.CreatePointerCast(call_g2l, nextInst->getOperand(0)->getType(), "castFromVoid*");
                                    nextInst->setOperand(0, castFromVoidStar);
                                }
                                else if (nextInst->getOpcode() == Instruction::Store && nextInst->getOperand(1)->getValueID() == inst->getValueID())
                                {
                                    // We have found a dereference of a pointer.  The next instruction is a store instruction and the current instructions value is the operand for the next instruction.
                                    IRBuilder<> builder(nextInst);
                                    Value *castToVoidStar = builder.CreatePointerCast(inst, Type::getInt8PtrTy(getGlobalContext()), "castToVoid*");
                                    Value *call_g2l = builder.CreateCall(g2l_function, castToVoidStar, "call__g2l");
                                    Value *castFromVoidStar = builder.CreatePointerCast(call_g2l, nextInst->getOperand(1)->getType(), "castFromVoid*");
                                    nextInst->setOperand(1, castFromVoidStar);
                                }
                            }// end find pointer to pointer operand
                        }// end for loop iterating over all operands
//                        if (CallInst *funcCall = dyn_cast<CallInst>(inst))
//                        {
//                            funcCall->print(errs());
//                            errs() << "\n";
//                            for (unsigned int argIndex = 0; argIndex < funcCall->getNumArgOperands(); ++argIndex)
//                            {
//                                if (funcCall->getArgOperand(argIndex)->getType()->isPointerTy())
//                                {
//                                    funcCall->getArgOperand(argIndex)->print(errs());
//                                    errs() << "\n";
//                                }
//                            }
//                        }
                    }// end for loop iterating over all instructions
                    //                    fItr->print(errs());
                }// end for loop iterating over all basic blocks
            }// end for loop iterating over all functions in a module
            return true;
        }
    };
}

char StackManagerPass::ID = 0; //Id the pass.
static RegisterPass<StackManagerPass> X("stk-mgmt", "Stack Management Pass"); //Register the pass.