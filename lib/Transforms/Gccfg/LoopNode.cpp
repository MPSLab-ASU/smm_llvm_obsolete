//
//  LoopNode.cpp
//  gccfgProject
//
//  Created by Bryce Holton on 8/6/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#include "LoopNode.h"

int LoopNode::loopNumId = 0;

LoopNode::LoopNode() : Node(NK_Loop)
{
    setLoopId(NULL);
    localId = LoopNode::loopNumId++;
}
LoopNode::~LoopNode()
{
    
}
void LoopNode::print()
{
//    errs() << "Node" << this << "[label=\"Loop\", shape=square]";
    errs() << "Loop_" << localId;
}
void LoopNode::printShape()
{
    errs() << "[shape=square];";
}
