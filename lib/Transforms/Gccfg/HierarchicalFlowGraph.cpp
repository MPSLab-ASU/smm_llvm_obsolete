//
//  HierarchicalFlowGraph.cpp
//  gccfgProject
//
//  Created by Bryce Holton on 8/5/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#include "HierarchicalFlowGraph.h"
#include "llvm/IR/IRBuilder.h"
#include <vector>

//void removeCommonItems(std::unordered_multiset<BasicBlock*> &ms1, std::unordered_multiset<BasicBlock*> &ms2, bool first)
//{
//    // Go through the first hash table
//    for (std::unordered_multiset<BasicBlock*>::iterator cims1 = ms1.cbegin(); cims1 != ms1.cend();)
//    {
//        // Find the current item in the second hash table
//        std::unordered_multiset<BasicBlock*>::iterator cims2 = ms2.find(*cims1);
//        
//        // Is it present?
//        if (cims2 != ms2.end())
//        {
//            // If so, remove it from hash table
//            if (first)
//            {
//                cims1 = ms1.erase(cims1);
//            }
//            else
//            {
//                ms2.erase(cims2);
//            }
//        }
//        else // If not
//        {
//            ++cims1; // Move on to the next item
//        }
//    }
//}
bool connectExitToLph(TerminatorInst* inst, BasicBlock* lph, BasicBlock *loopExitBlock, Loop *loop)
{
    if (inst != NULL)
    {
        BranchInst::Create(loop->getExitBlock(), lph);
        for (unsigned int i = 0; i < inst->getNumSuccessors(); ++i)
        {
            if (inst->getSuccessor(i) != loop->getExitBlock())
            {
                BranchInst::Create(inst->getSuccessor(i), loopExitBlock);
                inst->eraseFromParent();
                if (!(inst = loopExitBlock->getTerminator()))
                {
                    loopExitBlock->print(errs());
                    errs() << "Error: Something went wrong modifying the terminator of the exit block\n";
                    return false;
                }
            }
        }
    }
    else
    {
        loopExitBlock->print(errs());
        errs() << "This loop's exit has a poorly formed basic block.  We need to fix this\n";
        return false;
    }
    return true;
}
bool connectHeaderToLph(TerminatorInst* inst, BasicBlock* lph)
{
    if (inst != NULL)
    {
        inst->setSuccessor(0, lph);
    }
    else
    {
        errs() << "This loop's header has a poorly formed basic block.  We need to fix this\n";
        return false;
    }
    return true;
}
bool HierarchicalFlowGraph::addLoopPlaceHolder(Loop *loop)
{
    BasicBlock *loopPreheader = loop->getLoopPreheader();
    SmallVector<BasicBlock*, 1> exitBlocks;
    loop->getExitingBlocks(exitBlocks);
    
    if (loopPreheader != NULL)
    {
        if (exitBlocks.size() == 1 || exitBlocks.size() == 0)
        {
            //We have an entrance block, but we might not have an exit block.
            BasicBlock* loopPlaceHolder = BasicBlock::Create(loopPreheader->getContext(), "loop_place_holder", loopPreheader->getParent());
            addLphMapPair(std::make_pair(loopPlaceHolder, loop));
            addBlockToBlockList(loopPlaceHolder);
            
            TerminatorInst* preHeaderTerminator = loopPreheader->getTerminator();
            if (!connectHeaderToLph(preHeaderTerminator, loopPlaceHolder))
            {
                loopPreheader->print(errs());
                return false;
            }
            if (exitBlocks.size() == 1)
            {
                TerminatorInst* exitTerminator = exitBlocks[0]->getTerminator();
                if (!connectExitToLph(exitTerminator, loopPlaceHolder, exitBlocks[0], loop))
                {
                    return false;
                }
            }
            else if (exitBlocks.size() == 0)
            {
                BranchInst::Create(this->exitBlock, loopPlaceHolder);
            }
        }
        else
        {
            loop->print(errs());
            errs() << "This loop has more than one exit.  We need to fix this\n";
            return false;
        }
    }
    else
    {
        loop->print(errs());
        errs() << "Loop Error: This loop has more than one preheader.  We need to fix this\n";
        return false;
    }
    return true;
}
void HierarchicalFlowGraph::constructHfgForFunction(Function* function, LoopInfo *loopInformation)
{
    for (Function::iterator blockItr = function->begin(); blockItr != function->end() && getBuildStatus(); ++blockItr)
    {
        if (Loop *testLoop = loopInformation->getLoopFor(blockItr))
        {
            if (testLoop->getLoopDepth() == 1 && testLoop->getHeader() == blockItr)
            {
                if (!addLoopPlaceHolder(testLoop))
                {
                    setBuildStatus(false);
                }
            }
        }
        else
        {
            // Build the list of blocks in this loop, anything not in a sub loop is a block in the top level loop.
            addBlockToBlockList(blockItr);
            if (blockItr->getTerminator()->getNumSuccessors() > 2)
            {
                if (!fixSwitchBlocks(blockItr))
                {
                    setBuildStatus(false);
                }
            }
        }
    }
    
}
bool HierarchicalFlowGraph::fixSwitchBlocks(BasicBlock* switchBlock)
{
    if (SwitchInst* swInst = dyn_cast<SwitchInst>(switchBlock->getTerminator()))
    {
        BasicBlock* firstIntermediateBlock = BasicBlock::Create(switchBlock->getContext(), "intermediate_block", switchBlock->getParent());
        BasicBlock* prevIntBlock = firstIntermediateBlock;
        addBlockToBlockList(firstIntermediateBlock);
        
        for (SwitchInst::CaseIt caseItr = swInst->case_begin(); caseItr != swInst->case_end(); ++caseItr)
        {
            BasicBlock* dest = caseItr.getCaseSuccessor();
            BasicBlock* intermediateBlock = BasicBlock::Create(switchBlock->getContext(), "intermediate_block", switchBlock->getParent());
            addBlockToBlockList(intermediateBlock);
            
            IRBuilder<> builder(prevIntBlock);
            Value* xEqualsY = builder.CreateICmpEQ(swInst->getCondition(), caseItr.getCaseValue());
            builder.CreateCondBr(xEqualsY, dest, intermediateBlock);
            prevIntBlock = intermediateBlock;
        }
        //Epilog
        BasicBlock* parent = prevIntBlock->getSinglePredecessor();
        parent->getTerminator()->setSuccessor(1, swInst->getDefaultDest());
        blockList.pop_back();
        prevIntBlock->eraseFromParent();
        //End epilog
        //Clean up.
        switchBlock->getTerminator()->eraseFromParent();
        BranchInst::Create(firstIntermediateBlock, switchBlock);
        //Finish Clean up.
    }
    else
    {
        errs() << "Somehow an instruction with more than 2 ancestors is not a switch, fix this\n";
        switchBlock->print(errs());
        return false;
    }
    return true;
}
void HierarchicalFlowGraph::constructHfgForLoop(Loop* loop)
{
    for (Loop::iterator loopItr = loop->begin(); loopItr != loop->end(); ++loopItr)
    {
        if ((*loopItr)->getLoopDepth() == getLevel())
        {
            if (!addLoopPlaceHolder(*loopItr))
            {
                setBuildStatus(false);
            }
        }
    }
}
void HierarchicalFlowGraph::buildBlockListForLoop(Loop* loop)
{
    std::vector<BasicBlock*> ms1(loop->getBlocks().begin(), loop->getBlocks().end());
    std::sort(ms1.begin(), ms1.end());
    
    for (Loop::iterator loopItr = loop->begin(); loopItr != loop->end(); ++loopItr)
    {
        std::vector<BasicBlock*> ms2((*loopItr)->getBlocks().begin(), (*loopItr)->getBlocks().end());
        std::sort(ms2.begin(), ms2.end());
        
        std::vector<BasicBlock*>::iterator endRange;
        endRange = set_difference(ms1.begin(), ms1.end(),
                                  ms2.begin(), ms2.end(),
                                  ms1.begin());
        ms1.erase(endRange, ms1.end());
    }
    for (std::vector<BasicBlock*>::iterator itr = ms1.begin(); itr != ms1.end(); ++itr)
    {
        addBlockToBlockList(*itr);
        if ((*itr)->getTerminator()->getNumSuccessors() > 2)
        {
            if (!fixSwitchBlocks(*itr))
            {
                setBuildStatus(false);
            }
        }
    }
}
BasicBlock* findExitBlock(Function *f)
{
    BasicBlock* returnBlock = NULL;
    
    for (Function::iterator blockItr = f->begin(); blockItr != f->end(); ++blockItr)
    {
        if ( blockItr->getTerminator()->getNumSuccessors() == 0 && dyn_cast<ReturnInst>( blockItr->getTerminator() ) )
        {
            if (returnBlock == NULL)
            {
                returnBlock = blockItr;
            }
            else
            {
                return NULL;
            }
        }
    }
    
    return returnBlock;
}
HierarchicalFlowGraph::HierarchicalFlowGraph(Function *function, LoopInfo *loopInformation)
{
    // Build an HFG for the function w/o any of its loops, we will refer to this as a top level loop from now on.
    exitBlock = findExitBlock(function);
    if (exitBlock)
    {
        setLevel(1);
        setBuildStatus(true);
        constructHfgForFunction(function, loopInformation);
        
        if (getBuildStatus()) //If this is false, something didn't go right while constructing hfg.
        {
            for (unsigned int i = 0; i < blockList.size(); ++i)
            {
                if ( blockList[i]->getTerminator()->getNumSuccessors() == 0 && !dyn_cast<ReturnInst>(blockList[i]->getTerminator()) )
                {
                    blockList[i]->getTerminator()->eraseFromParent();
                    BranchInst::Create(exitBlock, blockList[i]);
                }
            }
        }
    }
    else
    {
        errs() << "Error: This function has multiple returns, we need to fix that.";
        setBuildStatus(false);
    }
}
HierarchicalFlowGraph::HierarchicalFlowGraph(Loop *loop)
{
    setBuildStatus(true);
    setLevel(loop->getLoopDepth() + 1);
    
    // Build an HFG for a loop inside a function.
    if (BasicBlock *latch = loop->getLoopLatch())
    {
        exitBlock = latch;
        addBlockToBlockList(exitBlock);
        addLphMapPair(std::make_pair(loop->getHeader(), loop));
        constructHfgForLoop(loop);
        buildBlockListForLoop(loop);
    }
    else
    {
        errs() << "Error: This loop has multiple latches.  Fix this\n";
        loop->print(errs());
        setBuildStatus(false);
    }
}
HierarchicalFlowGraph::~HierarchicalFlowGraph()
{

}
