//
//  ConditionNode.cpp
//  gccfgProject
//
//  Created by Bryce Holton on 8/6/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#include "ConditionNode.h"
#include "FunctionNode.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include <set>

bool truePath;
std::vector<BasicBlock*> currentPath;

int ConditionNode::conditionId = 0;

ConditionNode::ConditionNode() : Node(NK_Condition)
{
    convergencePoint = NULL;
    localId = ConditionNode::conditionId++;
}
ConditionNode::~ConditionNode()
{
    
}
void ConditionNode::printEdges()
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
        if (std::find(falseEdges.begin(), falseEdges.end(), edgeSet) == falseEdges.end())
        {
            errs() << "[tailport=sw];";
        }
        else
        {
            errs() << "[tailport=se];";
        }
        errs() << "\n";
        edgeSet = edgeSet->getNextEdge();
    }
}
void ConditionNode::printShape()
{
    errs() << "[shape=diamond];";
}
void ConditionNode::print()
{
//    errs() << "Node" << this << "[label=\"Condition\", shape=diamond]";
    errs() << "Condition_" << localId;
}
void ConditionNode::addTrueEdge(Edge* trueEdge)
{
    trueEdges.push_back(trueEdge);
}
void ConditionNode::addFalseEdge(Edge* falseEdge)
{
    falseEdges.push_back(falseEdge);
}
void depthFirstSearch(BasicBlock *block, std::vector< std::vector<BasicBlock*> > &blockPaths)
{
    currentPath.push_back(block);
    if (block->getTerminator()->getNumSuccessors() == 0 || block->getName().find("exit_block") != std::string::npos)
    {
        blockPaths.push_back(currentPath);
        currentPath.clear();
    }
    if (block->getName().find("exit_block") == std::string::npos)
    {
        for (unsigned int i = 0; i < block->getTerminator()->getNumSuccessors(); ++i)
        {
            depthFirstSearch(block->getTerminator()->getSuccessor(i), blockPaths);
        }
    }
}
BasicBlock* sortThroughBlockLists(std::vector< std::vector<BasicBlock*> > smallerList, std::vector< std::vector<BasicBlock*> > biggerList)
{
    std::vector<BasicBlock*> finalList;
    std::vector<BasicBlock*> testList = smallerList[0];

    for (unsigned int j = 0; j < testList.size(); j++)
    {
        bool blockFound = true;
        for (unsigned int i = 1; blockFound && i < smallerList.size(); i++)
        {
            if (std::find(smallerList[i].begin(), smallerList[i].end(), testList[j]) == smallerList[i].end())
            {
                blockFound = false;
            }
        }
        for (unsigned int i = 0; blockFound && i < biggerList.size(); i++)
        {
            if (std::find(biggerList[i].begin(), biggerList[i].end(), testList[j]) == biggerList[i].end())
            {
                blockFound = false;
            }
        }
        if (blockFound)
        {
            finalList.push_back(testList[j]);
        }
    }
    if (finalList.size() > 0)
    {
        return finalList[0];
    }
    else
    {
        return NULL;
    }
}
BasicBlock* findLowestCommonAncestor(BasicBlock* conditionBlock)
{
    std::vector< std::vector<BasicBlock*> > trueBlocks;
    std::vector< std::vector<BasicBlock*> > falseBlocks;
    BasicBlock* lcaBlock = NULL;
    
    depthFirstSearch(conditionBlock->getTerminator()->getSuccessor(0), trueBlocks);
    depthFirstSearch(conditionBlock->getTerminator()->getSuccessor(1), falseBlocks);
    
    if (trueBlocks.size() < falseBlocks.size())
    {
        lcaBlock = sortThroughBlockLists(trueBlocks, falseBlocks);
    }
    else
    {
        lcaBlock = sortThroughBlockLists(falseBlocks, trueBlocks);
    }
    return lcaBlock;
}
void ConditionNode::dfsFindBlocksOfInterest(BasicBlock* block, Graph* graph, BasicBlock* nestedConvergencePoint)
{
    if (block != this->getConvergencePoint())
    {
        if (nestedConvergencePoint != NULL && block == nestedConvergencePoint)
        {
            nestedConvergencePoint = NULL;
        }
        else if (nestedConvergencePoint == NULL)
        {
            std::vector<Node*> nodeList = compareBlockToNodeList(graph->getNodeList(), block);
            
            for (unsigned int i = 0; i < nodeList.size(); ++i)
            {
                if (ConditionNode* cNode = dyn_cast<ConditionNode>(nodeList[i]))
                {
                    nestedConvergencePoint = cNode->getConvergencePoint();
                }
                Edge* newEdge = graph->addEdge(this, nodeList[i]);
                if (truePath)
                {
                    addTrueEdge(newEdge);
                }
                else
                {
                    addFalseEdge(newEdge);
                }
                if (FunctionNode* fNode = dyn_cast<FunctionNode>(nodeList[i]))
                {
                    if (fNode->getFunctionPointer())
                    {
                        newEdge->setPointerEdge(true);
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
}
bool ConditionNode::setConvergencePoint()
{
    if (( convergencePoint = findLowestCommonAncestor( getMappedBlock() ) ) != NULL)
    {
        return true;
    }
    else
    {
        errs() << "Error: cannot find a convergence point for basic block. Exiting building gccfg.\nFunction: " << getMappedBlock()->getParent()->getName();
        getMappedBlock()->print(errs());
        return false;
    }
}
void ConditionNode::createEdges(Graph* thisGraph)
{
    truePath = true;
    dfsFindBlocksOfInterest(getMappedBlock()->getTerminator()->getSuccessor(0), thisGraph, NULL);
    truePath = false;
    dfsFindBlocksOfInterest(getMappedBlock()->getTerminator()->getSuccessor(1), thisGraph, NULL);
}
