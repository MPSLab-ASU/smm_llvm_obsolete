//===- ExtractFunction.cpp - Extract a function from Program --------------===//
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
    struct SPTest : public ModulePass
    {
        static char ID; // Pass identification, replacement for typeid
        
        // Pass constructor
        SPTest() : ModulePass(ID)
        {}
        
        // Pass destructor
        ~SPTest()
        {}
        
        virtual bool runOnModule (Module &M)
        {
//            Function *test_func = cast<Function>(M.getOrInsertFunction("test_func", Type::getInt32Ty(getGlobalContext()), (Type *)0));
//            test_func->setCallingConv(CallingConv::C);
//            BasicBlock* BB = BasicBlock::Create(getGlobalContext(), "EntryBlock", test_func);
//            IRBuilder<> builder(BB);
//            Value *zero = builder.getInt32(0);
//            builder.CreateRet(zero);
            
            for (Module::iterator functionItr = M.begin(); functionItr != M.end(); ++functionItr)
            {
                for (Function::iterator blockItr = functionItr->begin(); blockItr != functionItr->end(); ++blockItr)
                {
                    for (BasicBlock::iterator instItr = blockItr->begin(); instItr != blockItr->end(); ++instItr)
                    {
                        errs() << *instItr << "\n";
//                        if (CallInst *functionCall = dyn_cast<CallInst>(instItr))
//                        {
//                            CallInst::Create (test_func, "",functionCall);
////                            errs() << *functionCall << "\n";
//                        }
                    }
                }
            }
            return true;
        }
    };
}  // end anonymous namespace

char SPTest::ID = 0;
static RegisterPass<SPTest>
X("stk-ptr-tst2", "Insert a dummy function, so we can see instructions inserted on the back-end.");
