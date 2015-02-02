//
//  Graph.h
//  gccfgProject
//
//  Created by Bryce Holton on 8/6/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#ifndef __gccfgProject__Graph__
#define __gccfgProject__Graph__

#include <iostream>
#include "Node.h"
#include "Edge.h"
#include <llvm/Support/raw_ostream.h>

class Node;
class Edge;

class Graph
{
private:
    Node* rootNode;
    bool buildStatus;
    
protected:
    Node *nodes;
    
public:
    Graph();
    ~Graph();
    void addNode(Node* node);
    bool replaceNode(Node* oldNode, Node* newNode);
    bool deleteNode(Node* node);
    Edge* addEdge(Node* parent, Node* child);
    void replaceEdge(Node* parent, Node* oldChild, Node* newChild);
    Edge* deleteEdge(Node* parent, Edge* edge);
    Node* getNodeList(){return nodes;}
    void setNodeList(Node* node){nodes = node;}
    void printGraph();
    void setRootNode(Node* node){rootNode = node;}
    Node* getRootNode(){return rootNode;}
    void resetVisitedNodes();
    void setBuildStatus(bool status){buildStatus = status;}
    bool getBuildStatus(){return buildStatus;}
};

#endif /* defined(__gccfgProject__Graph__) */
