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
    struct StackFrameManagerPass : public ModulePass
    {
        static char ID; // Pass identification, replacement for typeid
        StackFrameManagerPass() : ModulePass(ID) {}
        
        virtual bool runOnModule(Module &M)
        {
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
                            Function *calledFunc;
                            if ((calledFunc = functionCall->getCalledFunction()) != NULL)
                            {
                                if (calledFunc->getName().compare("__g2l") != 0 && calledFunc->getName().compare("__l2g") != 0 &&
                                    calledFunc != sstore_function && calledFunc != sload_function)
                                {
                                    CallInst::Create (sstore_function, "", functionCall);
                                    CallInst::Create (sload_function, "", nextInst);
                                }
                            }
                        }
                    }
                }// end for loop iterating over all basic blocks
            }// end for loop iterating over all functions in a module
            return true;
        }
    };
}

char StackFrameManagerPass::ID = 0; //Id the pass.
static RegisterPass<StackFrameManagerPass> X("stk-frm-mgmt", "Stack Frame Management Pass"); //Register the pass.