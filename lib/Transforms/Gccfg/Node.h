//
//  Node.h
//  gccfgProject
//
//  Created by Bryce Holton on 8/6/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#ifndef __gccfgProject__Node__
#define __gccfgProject__Node__

#include <iostream>
#include <llvm/IR/BasicBlock.h>
#include "llvm/Support/raw_ostream.h"
#include "Edge.h"
#include "Graph.h"
#include "llvm/Support/Casting.h"

using namespace llvm;

class Edge;
class Graph;

class Node
{
public:
    enum NodeKind
    {
        NK_Condition,
        NK_Function,
        NK_Loop
    };
    enum Color
    {
        WHITE,
        GREY,
        BLACK
    };
    virtual ~Node();
    void setMappedBlock(BasicBlock* block){mappedBlock = block;}
    BasicBlock* getMappedBlock(){return mappedBlock;}
    void setVisited(bool state){visited = state;}
    bool getVisited(){return visited;}
    void addEdge(Edge* newEdge);
    void deleteEdge(Edge* oldEdge);
    Edge* getEdges(){return edges;}
    void setNextNode(Node* node){nextNode = node;}
    Node* getNextNode(){return nextNode;}
    virtual void print() = 0;
    virtual void createEdges(Graph*);
    virtual void printShape();
    virtual void printEdges();
    
private:
    BasicBlock* mappedBlock;
    bool visited;
    Edge* edges;
    Node* nextNode;
    const NodeKind kind;
    int color;
    
protected:
    virtual void dfsFindBlocksOfInterest(BasicBlock*, Graph*, BasicBlock*);
    std::vector<Node*> compareBlockToNodeList(Node*, BasicBlock*);
    
public:
    Node(NodeKind k);
    NodeKind getKind() const { return kind; }
    void setColor(Color c){color = c;}
    int getColor(){return color;}
    
};

#endif /* defined(__gccfgProject__Node__) */
