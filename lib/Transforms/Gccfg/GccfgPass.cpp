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
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopInfo.h"
#include "HierarchicalFlowGraph.h"
#include "CallControlFlowGraph.h"
#include "GlobalCallControlFlowGraph.h"

using namespace llvm;

namespace
{
    struct GccfgPass : public FunctionPass
    {
        static char ID; // Pass identification, replacement for typeid
        GccfgPass() : FunctionPass(ID) {}
        
        std::vector<CallControlFlowGraph*> ccfgs;
        
        virtual void getAnalysisUsage(AnalysisUsage &Info) const
        {
            Info.setPreservesCFG();
            Info.addRequired<LoopInfo>();
        }
        bool insertExitBlock(Loop* loop, LoopInfo *loopInfo)
        {
            BasicBlock* exitBlock = BasicBlock::Create(loop->getHeader()->getContext(), "exit_block", loop->getHeader()->getParent());
            loop->addBasicBlockToLoop(exitBlock, loopInfo->getBase());
            
            if (BasicBlock* latch = loop->getLoopLatch())
            {
                TerminatorInst* term = latch->getTerminator();
                
                if (BranchInst* branch = dyn_cast<BranchInst>(term))
                {
                    BranchInst::Create(branch->getSuccessor(0), exitBlock);
                    branch->setSuccessor(0, exitBlock);
                }
                else
                {
                    errs() << "Error: We do not have a looplatch branch in this loop \n";
                    latch->print(errs());
                    return false;
                }
            }
            else
            {
                SmallVector<BasicBlock*, 1> latches;
                loop->getLoopLatches(latches);
                errs() << "Error: This loop has multiple latches.  Fix this\n";
                loop->print(errs());
                return false;
            }
            return true;
        }
        void verifySingleLoopExit(Loop* loop, LoopInfo* loopInfo)
        {
            SmallVector<BasicBlock*, 1> exitingBlocks; //Blocks with edge leading out of the loop
            loop->getExitingBlocks(exitingBlocks);
            
            if (exitingBlocks.size() > 1)
            {
                SmallVector<BasicBlock*, 1> exitBlocks; //Blocks with parents inside of the loop
                loop->getExitBlocks(exitBlocks);
                
                for (unsigned int i = 0; i < exitBlocks.size(); ++i)
                {
                    for (BasicBlock::iterator instItr = exitBlocks[i]->begin(); instItr != exitBlocks[i]->end(); ++instItr)
                    {
                        if (CallInst* fCall = dyn_cast<CallInst>(instItr))
                        {
                            if (fCall->getCalledFunction()->getName().compare("exit") == 0)
                            {
                                // We found an exit function call.
                                loopInfo->removeBlock(exitBlocks[i]);
                                loop->addBasicBlockToLoop(exitBlocks[i], loopInfo->getBase());
                                exitBlocks[i]->getTerminator()->eraseFromParent();
                                BranchInst::Create(loop->getLoopLatch(), exitBlocks[i]);
                            }
                        }
                    }
                }
            }
        }
        bool verifyLoopStructure(LoopInfo *loopInfo)
        {
            for (LoopInfo::iterator loopItr = loopInfo->begin(); loopItr != loopInfo->end(); ++loopItr)
            {
                if (!insertExitBlock(*loopItr, loopInfo))
                {
                    return false;
                }
                verifySingleLoopExit(*loopItr, loopInfo);
                for (Loop::iterator subLoopItr = (*loopItr)->begin(); subLoopItr != (*loopItr)->end(); ++subLoopItr)
                {
                    if (!insertExitBlock(*subLoopItr, loopInfo))
                    {
                        return false;
                    }
                    verifySingleLoopExit(*subLoopItr, loopInfo);
                }
            }
            return true;
        }
        void buildHfgs(Function *function, LoopInfo *loopInfo, std::vector<HierarchicalFlowGraph*> &hfgs)
        {
            HierarchicalFlowGraph* functionHfg = new HierarchicalFlowGraph(function, loopInfo);
            hfgs.push_back(functionHfg);
            for (LoopInfo::iterator loopItr = loopInfo->begin(); loopItr != loopInfo->end(); ++loopItr)
            {
                HierarchicalFlowGraph* loopHfg = new HierarchicalFlowGraph(*loopItr);
                hfgs.push_back(loopHfg);
                for (Loop::iterator subLoopItr = (*loopItr)->begin(); subLoopItr != (*loopItr)->end(); ++subLoopItr)
                {
                    HierarchicalFlowGraph* subLoopHfg = new HierarchicalFlowGraph(*subLoopItr);
                    hfgs.push_back(subLoopHfg);
                    (*loopItr)->removeChildLoop(subLoopItr--);
                }
            }
        }
        void buildCcfgs(std::vector<HierarchicalFlowGraph*> &hfgs)
        {
            for (unsigned int i = 0; i < hfgs.size(); ++i)
            {
                ccfgs.push_back(new CallControlFlowGraph(hfgs[i]));
            }
        }
        virtual bool runOnFunction(Function &F)
        {
//            F.viewFG();
            std::vector<HierarchicalFlowGraph*> hfgs;
            
            // Given a set of CFGs we must extract the loop information from them.
            LoopInfo &loopInformation = getAnalysis<LoopInfo>();
            
            // Once the loop information is extrated we build hfgs
            if (verifyLoopStructure(&loopInformation))
            {
                buildHfgs(&F, &loopInformation, hfgs);
//                F.viewCFG();
            
                // Once the hfgs are built, we build a ccfg for each one.
                buildCcfgs(hfgs);
            }
            
            
            // Clean up
            for (unsigned int i = 0; i < hfgs.size(); ++i)
            {
                delete hfgs[i];
            }
            return false;
        }
        virtual bool doFinalization(Module &M)
        {
            // Stitch all ccfgs together to make gccfg.
            GlobalCallControlFlowGraph gccfg(ccfgs);
            
            if (gccfg.getBuildStatus())
            {
                gccfg.printGraph();
                // Clean up more
                for (unsigned int i = 0; i < ccfgs.size(); ++i)
                {
                    ccfgs[i]->setNodeList(NULL);
                    delete ccfgs[i];
                }
            }
            else
            {
                // Clean up more
                for (unsigned int i = 0; i < ccfgs.size(); ++i)
                {
                    delete ccfgs[i];
                }
            }
            
            return false;
        }
    };
}

char GccfgPass::ID = 0;
static RegisterPass<GccfgPass> X("GccfgPass", "Gccfg Pass");

