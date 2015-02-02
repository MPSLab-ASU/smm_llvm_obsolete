//
//  LoopNode.h
//  gccfgProject
//
//  Created by Bryce Holton on 8/6/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#ifndef __gccfgProject__LoopNode__
#define __gccfgProject__LoopNode__

#include <iostream>
#include "Node.h"
#include "llvm/Analysis/LoopInfo.h"

class LoopNode : public Node
{
private:
    Loop* loopId;
    static int loopNumId;
    int localId;
    
public:
    LoopNode();
    virtual ~LoopNode();
    void setLoopId(Loop* id){loopId = id;}
    Loop* getLoopId(){return loopId;}
    virtual void print();
    virtual void printShape();
    static bool classof(const Node *n) {return n->getKind() == NK_Loop;}
};

#endif /* defined(__gccfgProject__LoopNode__) */
