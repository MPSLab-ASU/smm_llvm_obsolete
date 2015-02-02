//
//  CallControlFlowGraph.h
//  gccfgProject
//
//  Created by Bryce Holton on 8/5/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#ifndef __gccfgProject__CallControlFlowGraph__
#define __gccfgProject__CallControlFlowGraph__

#include <iostream>
#include "HierarchicalFlowGraph.h"
#include "Graph.h"

class CallControlFlowGraph : public Graph
{
    bool createGraphVertexes(HierarchicalFlowGraph *hfg);
    bool createConditionVertexes(std::vector<BasicBlock*> blockList);
    bool createFunctionVertexes(std::vector<BasicBlock*>, unsigned int );
    bool findConvergencePointsForConditionNodes();
    bool createLoopVertexes(LphType);
    void createGraphEdges();
    void recursivePointerTargets(Instruction*, BasicBlock*);
    
public:
    CallControlFlowGraph(HierarchicalFlowGraph *);
    ~CallControlFlowGraph();
};

#endif /* defined(__gccfgProject__CallControlFlowGraph__) */
