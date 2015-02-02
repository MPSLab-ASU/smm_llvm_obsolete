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

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace
{
    struct GlobalCfgPass : public ModulePass
    {
        static char ID; // Pass identification, replacement for typeid
        GlobalCfgPass() : ModulePass(ID) {}
        
        virtual bool runOnModule(Module &M)
        {
            for (Module::iterator functions = M.begin(); functions != M.end(); ++functions)
            {
                errs() << functions->getName() << "\n";
                for (Function::iterator basicBlocks = functions->begin(); basicBlocks != functions->end(); ++basicBlocks)
                {
                    Function* calledFunction = nullptr;
                    for (BasicBlock::iterator instructions = basicBlocks->begin(); instructions != basicBlocks->end(); ++instructions)
                    {
                        if (calledFunction)
                        {
                            if (!calledFunction->empty())
                            {
                                BasicBlock* newChildBlock = basicBlocks->splitBasicBlock(instructions);
                                TerminatorInst* term = basicBlocks->getTerminator();
                                
                                errs() << basicBlocks->getName() << "\n";
                                
                                ++basicBlocks;
                            }
                            calledFunction = nullptr;
                        }
                        if (CallInst* callInstruction = dyn_cast<CallInst>(instructions))
                        {
                            calledFunction = callInstruction->getCalledFunction();
                        }
                    }
                }
                functions->viewCFGOnly();
            }
            return false;
        }
    };
}

char GlobalCfgPass::ID = 0;
static RegisterPass<GlobalCfgPass> X("GlobalCfgPass", "Global CFG Pass");

