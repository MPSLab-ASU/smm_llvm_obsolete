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
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace
{
    struct MainFunctionCreator : public ModulePass
    {
        static char ID; // Pass identification, replacement for typeid
        MainFunctionCreator() : ModulePass(ID) {}
        
        virtual bool runOnModule(Module &M)
        {
            ValueToValueMapTy VMap;

            for (Module::iterator I = M.begin(); I != M.end(); ++I)
            {
                if (I->getName().compare("main") == 0)
                {
                    // Create an external function called smm_main
                    Function *NF = Function::Create(cast<FunctionType>(I->getType()->getElementType()), I->getLinkage(), "smm_main", &M);
                    NF->copyAttributesFrom(I);
                    VMap[I] = NF;
                    std::vector<Value*> ArgsV;
                    
                    // copy the function body from main to smm_main
                    if (!I->isDeclaration())
                    {
                        Function::arg_iterator DestI = NF->arg_begin();
                        for (Function::arg_iterator J = I->arg_begin(); J != I->arg_end(); ++J)
                        {
                            DestI->setName(J->getName());
                            VMap[J] = DestI++;
                            ArgsV.push_back(J);
                        }
                        
                        SmallVector<ReturnInst*, 8> Returns;  // Ignore returns cloned.
                        CloneFunctionInto(NF, I, VMap, /*ModuleLevelChanges=*/true, Returns);
                    }
                    
                    // delete all the basic blocks in main
                    std::vector<BasicBlock*> blockList;
                    for (Function::iterator F = I->begin(); F != I->end(); ++F)
                    {
                        for (BasicBlock::iterator B = F->begin(); B != F->end(); ++B)
                        {
                            B->dropAllReferences(); //Make sure there are no uses of any instruction
                        }
                        blockList.push_back(F);
                    }
                    for (unsigned int i = 0; i < blockList.size(); ++i)
                    {
                        blockList[i]->eraseFromParent();
                    }
                    
                    // create one basic block with a return 0 instruction in main
                    BasicBlock* BB = BasicBlock::Create(getGlobalContext(), "EntryBlock", I);
                    IRBuilder<> builder(BB);
                    builder.CreateCall(NF,ArgsV);
                    Value *zero = builder.getInt32(0);
                    builder.CreateRet(zero);
                }
                
            }
            return true;
        }
    };
}

char MainFunctionCreator::ID = 0; //Id the pass.
static RegisterPass<MainFunctionCreator> X("crt-main-func", "Create a new main function"); //Register the pass.