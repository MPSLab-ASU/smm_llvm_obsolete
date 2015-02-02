//
//  Edge.h
//  gccfgProject
//
//  Created by Bryce Holton on 8/6/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#ifndef __gccfgProject__Edge__
#define __gccfgProject__Edge__

#include <iostream>
#include "Node.h"

class Node;

class Edge
{
private:
    Node *connectsTo;
    Edge *nextEdge;
    bool backEdge;
    bool pointerEdge;
    
public:
    Edge();
    ~Edge();
    void setConnectsTo(Node* node){connectsTo = node;}
    Node* getConnectsTo(){return connectsTo;}
    void setNextEdge(Edge* edge){nextEdge = edge;}
    Edge* getNextEdge(){return nextEdge;}
    void setBackEdge(bool edgeType){backEdge = edgeType;}
    bool getBackEdge(){return backEdge;}
    void setPointerEdge(bool pEdge){pointerEdge = pEdge;}
    bool getPointerEdge(){return pointerEdge;}
};

#endif /* defined(__gccfgProject__Edge__) */
