//
//  Graph.cpp
//  gccfgProject
//
//  Created by Bryce Holton on 8/6/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#include "Graph.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Function.h"

Graph::Graph()
{
    nodes = NULL;
    setRootNode(NULL);
    setBuildStatus(false);
}
Graph::~Graph()
{
    if (nodes != NULL)
    {
        Node *nextNode = nodes->getNextNode();
        while (nextNode != NULL)
        {
            delete nodes;
            nodes = nextNode;
            nextNode = nextNode->getNextNode();
        }
        delete nodes;
        nodes = NULL;
    }
}
void Graph::addNode(Node* node)
{
    if (getNodeList() == NULL)
    {
        nodes = node;
    }
    else
    {
        Node* nextNode = getNodeList();
        
        while (nextNode->getNextNode() != NULL)
        {
            nextNode = nextNode->getNextNode();
        }
        nextNode->setNextNode(node);
    }
}
bool Graph::replaceNode(Node* oldNode, Node* newNode)
{
    Node* node = getNodeList();
    Node* prevNode = NULL;
    
    while (node != NULL)
    {
        if (node == oldNode)
        {
            if (prevNode)
            {
                prevNode->setNextNode(newNode);
                newNode->setNextNode(oldNode->getNextNode());
            }
            else
            {
                newNode->setNextNode(oldNode->getNextNode());
            }
            oldNode->setNextNode(NULL);
            delete oldNode;
            return true;
        }
        prevNode = node;
        node = node->getNextNode();
    }
    return false;
}
Edge* Graph::addEdge(Node* parent, Node* child)
{
    Node* node = getNodeList();
    Edge* newEdge = NULL;
    
    while (node != NULL)
    {
        if (parent == node)
        {
            newEdge = new Edge();
            newEdge->setConnectsTo(child);
            parent->addEdge(newEdge);  
            return newEdge;
        }
        node = node->getNextNode();
    }
    return newEdge;
}
void Graph::replaceEdge(Node* parent, Node* oldChild, Node* newChild)
{
    Edge* pEdges = parent->getEdges();
    
    while (pEdges != NULL)
    {
        if (pEdges->getConnectsTo() == oldChild)
        {
            pEdges->setConnectsTo(newChild);
        }
        pEdges = pEdges->getNextEdge();
    }
}
bool Graph::deleteNode(Node* node)
{
    if (getNodeList() != NULL)
    {
        Node* prevNode = getNodeList();
        
        if (prevNode == node)
        {
            nodes = node->getNextNode();
            node->setNextNode(NULL);
            delete node;
            return true;
        }
        else
        {
            while (prevNode != NULL)
            {
                if (prevNode->getNextNode() == node)
                {
                    Node* currentNode = prevNode->getNextNode();
                    
                    prevNode->setNextNode(currentNode->getNextNode());
                    delete currentNode;
                    return true;
                }
                prevNode = prevNode->getNextNode();
            }
        }
    }
    return false;
}
Edge* Graph::deleteEdge(Node* parent, Edge* edge)
{
    Node* node = getNodeList();
    Edge* nextEdge = NULL;
    
    while (node != NULL)
    {
        if (parent == node)
        {
            nextEdge = edge->getNextEdge();
            parent->deleteEdge(edge);
            return nextEdge;
        }
        node = node->getNextNode();
    }
    return nextEdge;
}
void Graph::printGraph()
{
    errs() << "digraph{\n";
    errs() << "ordering=out;\n";
    
    Node* node = getNodeList();
    while (node != NULL)
    {
        node->print();
        node->printShape();
        errs() << "\n";
        node->printEdges();
        node = node->getNextNode();
    }
    errs() << "}\n\n";
}
void Graph::resetVisitedNodes()
{
    Node* node = getNodeList();
    while (node != NULL)
    {
        node->setVisited(false);
//        node->setColor(Node::WHITE);
        node = node->getNextNode();
    }
}

