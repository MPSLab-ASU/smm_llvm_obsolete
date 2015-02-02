//
//  GlobalCallControlFlowGraph.h
//  gccfgProject
//
//  Created by Bryce Holton on 8/5/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#ifndef __gccfgProject__GlobalCallControlFlowGraph__
#define __gccfgProject__GlobalCallControlFlowGraph__

#include <iostream>
#include "CallControlFlowGraph.h"
#include "Graph.h"

class GlobalCallControlFlowGraph : public Graph
{
private:
    void buildGccfg(std::vector<CallControlFlowGraph*> graphs);
    void cleanUpGccfg(Node*);
    void findBackEdges(Node* node);
    
public:
    GlobalCallControlFlowGraph(std::vector<CallControlFlowGraph*>);
    ~GlobalCallControlFlowGraph();
};

#endif /* defined(__gccfgProject__GlobalCallControlFlowGraph__) */
