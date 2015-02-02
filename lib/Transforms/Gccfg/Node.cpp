//
//  Node.cpp
//  gccfgProject
//
//  Created by Bryce Holton on 8/6/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#include "Node.h"
#include "ConditionNode.h"
#include "FunctionNode.h"
#include "llvm/IR/Instructions.h"

class ConditionNode;

Node::Node(NodeKind k) : kind(k)
{
    setMappedBlock(NULL);
    setVisited(false);
    setNextNode(NULL);
    edges = NULL;
    setColor(WHITE);
}
Node::~Node()
{
    setNextNode(NULL);
    if (edges != NULL)
    {
        Edge *nextEdge = edges->getNextEdge();
        while (nextEdge != NULL)
        {
            delete edges;
            edges = nextEdge;
            nextEdge = nextEdge->getNextEdge();
        }
        delete edges;
        edges = NULL;
    }
}
void Node::addEdge(Edge* newEdge)
{
    if (getEdges() == NULL)
    {
        edges = newEdge;
    }
    else
    {
        Edge* nextEdge = getEdges();
        
        while (nextEdge->getNextEdge() != NULL)
        {
            nextEdge = nextEdge->getNextEdge();
        }
        nextEdge->setNextEdge(newEdge);
    }
}
void Node::deleteEdge(Edge* oldEdge)
{
    if (getEdges() != NULL)
    {
        if (oldEdge == getEdges())
        {
            edges = oldEdge->getNextEdge();
            oldEdge->setNextEdge(NULL);
        }
        else
        {
            Edge* prevEdge = getEdges();
            
            while (prevEdge != NULL)
            {
                if (prevEdge->getNextEdge() == oldEdge)
                {
                    prevEdge->setNextEdge(oldEdge->getNextEdge());
                    oldEdge->setNextEdge(NULL);
                    delete oldEdge;
                }
                prevEdge = prevEdge->getNextEdge();
            }
        }
    }
}
void Node::printShape()
{
    
}
void Node::printEdges()
{
    Edge* edgeSet = getEdges();
    
    while (edgeSet != NULL)
    {
        print();
        errs() << "->";
//        errs() << "Node" << this << "->" << "Node" << edgeSet->getConnectsTo();
        edgeSet->getConnectsTo()->print();
        if (edgeSet->getBackEdge())
        {
            errs() << "[style=dotted]";
        }
        else if (edgeSet->getPointerEdge())
        {
            errs() << "[style=dashed]";
        }
        errs() << "[tailport=s];\n";
        edgeSet = edgeSet->getNextEdge();
    }
}
void Node::print()
{
    errs() << "Mapped Block ";
    getMappedBlock()->print(errs());
}
std::vector<Node*> Node::compareBlockToNodeList(Node* rootNode, BasicBlock* blockToCompare)
{
    std::vector<Node*> nodeList;
    while (rootNode != NULL)
    {
        if (rootNode->getMappedBlock() == blockToCompare)
        {
            nodeList.push_back(rootNode);
        }
        rootNode = rootNode->getNextNode();
    }
    return nodeList;
}
void Node::createEdges(Graph* graph)
{
    if (graph->getRootNode() == this)
    {
        dfsFindBlocksOfInterest(getMappedBlock(), graph, NULL);
    }
}
void Node::dfsFindBlocksOfInterest(BasicBlock* block, Graph* graph, BasicBlock* nestedConvergencePoint)
{
    if (nestedConvergencePoint != NULL && block == nestedConvergencePoint)
    {
        nestedConvergencePoint = NULL;
    }
    if (nestedConvergencePoint == NULL)
    {
        std::vector<Node*> nodeList = compareBlockToNodeList(graph->getNodeList(), block);
        
        for (unsigned int i = 0; i < nodeList.size(); ++i)
        {
            if (nodeList[i] != this)
            {
                if (ConditionNode* cNode = dyn_cast<ConditionNode>(nodeList[i]))
                {
                    nestedConvergencePoint = cNode->getConvergencePoint();
                }
                if (!nodeList[i]->getVisited())
                {
                    Edge* newEdge = graph->addEdge(this, nodeList[i]);
                    nodeList[i]->setVisited(true);
                    if (FunctionNode* fNode = dyn_cast<FunctionNode>(nodeList[i]))
                    {
                        if (fNode->getFunctionPointer())
                        {
                            newEdge->setPointerEdge(true);
                        }
                    }
                }
            }
        }
    }
    if (block->hasName() && block->getName().find("exit_block") == std::string::npos)
    {
        for (unsigned int i = 0; i < block->getTerminator()->getNumSuccessors(); ++i)
        {
            dfsFindBlocksOfInterest(block->getTerminator()->getSuccessor(i), graph, nestedConvergencePoint);
        }
    }
}
