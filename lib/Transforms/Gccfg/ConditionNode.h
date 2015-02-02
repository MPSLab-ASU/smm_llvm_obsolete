//
//  ConditionNode.h
//  gccfgProject
//
//  Created by Bryce Holton on 8/6/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#ifndef __gccfgProject__ConditionNode__
#define __gccfgProject__ConditionNode__

#include <iostream>
#include "Node.h"

class Node;

class ConditionNode : public Node
{
    std::vector<Edge*> trueEdges;
    std::vector<Edge*> falseEdges;
    BasicBlock* convergencePoint;
    static int conditionId;
    int localId;
    
    virtual void dfsFindBlocksOfInterest(BasicBlock*, Graph*, BasicBlock*);
    
public:
    ConditionNode();
    virtual ~ConditionNode();
    virtual void print();
    virtual void printShape();
    virtual void printEdges();
    virtual void createEdges(Graph*);
    void addTrueEdge(Edge* trueEdge);
    void addFalseEdge(Edge* falseEdge);
    std::vector<Edge*> getTrueEdges(){return trueEdges;}
    std::vector<Edge*> getFalseEdges(){return falseEdges;}
    bool setConvergencePoint();
    BasicBlock* getConvergencePoint(){return convergencePoint;}
    static bool classof(const Node *n) {return n->getKind() == NK_Condition;}
};

#endif /* defined(__gccfgProject__ConditionNode__) */
