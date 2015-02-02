//
//  HierarchicalFlowGraph.h
//  gccfgProject
//
//  Created by Bryce Holton on 8/5/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#ifndef __gccfgProject__HierarchicalFlowGraph__
#define __gccfgProject__HierarchicalFlowGraph__

#include <iostream>
#include "llvm/IR/Function.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/raw_ostream.h"
#include <llvm/IR/Instructions.h>

using namespace llvm;

typedef std::vector< std::pair<BasicBlock*, Loop*> > LphType;

class HierarchicalFlowGraph
{
private:
    unsigned int level;
    bool buildStatus;
    LphType lphMap;
    std::vector<BasicBlock*> blockList;
    BasicBlock* exitBlock;
    
    void setBuildStatus(bool status){buildStatus = status;}
    void addLphMapPair(std::pair<BasicBlock*, Loop*> newPair){lphMap.push_back(newPair);}
    bool addLoopPlaceHolder(Loop *loop);
    void addBlockToBlockList(BasicBlock* block){blockList.push_back(block);}
    void buildBlockListForLoop(Loop* loop);
    void constructHfgForLoop(Loop* loop);
    void constructHfgForFunction(Function* , LoopInfo*);
    bool connectToExitBlock(BasicBlock* currentExitBlock);
    bool fixSwitchBlocks(BasicBlock* switchBlock);
    
public:
    HierarchicalFlowGraph(Function *, LoopInfo *);
    HierarchicalFlowGraph(Loop *);
    ~HierarchicalFlowGraph();
    void setLevel(unsigned int lev){level = lev;}
    unsigned int getLevel(){return level;}
    bool getBuildStatus(){return buildStatus;}
    LphType getLphMap(){return lphMap;}
    std::vector<BasicBlock*> getBlockList(){return blockList;}
    void buildLoopHFG();
};

#endif /* defined(__gccfgProject__HierarchicalFlowGraph__) */
