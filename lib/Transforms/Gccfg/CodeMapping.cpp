//
//  CodeMapping.cpp
//  gccfgProject
//
//  Created by Bryce Holton on 10/20/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#include "CodeMapping.h"
#include "FunctionNode.h"
#include <limits>

CodeMapping::CodeMapping(int spmSize, std::map<std::string, int> fSizes) : SPM_SIZE(spmSize), FUNCTION_SIZES(fSizes)
{
    totalRegionsSize = 0;
    spmRegions = 0;
    for (std::map<std::string, int>::const_iterator functionItr = FUNCTION_SIZES.begin(); functionItr != FUNCTION_SIZES.end(); ++functionItr)
    {
        std::vector<std::string> newRegion;
        newRegion.push_back(functionItr->first);
        functionMapping.push_back(newRegion);
        spmRegions++;
        totalRegionsSize += functionItr->second;
    }
}
CodeMapping::~CodeMapping()
{
    
}
void CodeMapping::EraseSpmRegion(int &dst)
{
    //erase unused region
    functionMapping.erase(functionMapping.begin() + dst - 1);
    
    //calc new total regions size
    totalRegionsSize = 0;
    for (unsigned int i = 0; i < functionMapping.size(); ++i)
    {
        totalRegionsSize += GetRegionSize(functionMapping[i]);
    }
}
void CodeMapping::MergeRegions(int &dst, int &src)
{
    for (unsigned int i = 0; i < functionMapping[src - 1].size(); ++i)
    {
        functionMapping[dst - 1].push_back(functionMapping[src - 1][i]);
    }
}
int CodeMapping::GetRegionSize(std::vector<std::string> &region)
{
    int returnValue = 0;
    
    for (unsigned int i = 0; i < region.size(); ++i)
    {
        if (FUNCTION_SIZES.find(region[i])->second > returnValue)
        {
            returnValue = FUNCTION_SIZES.find(region[i])->second;
        }
    }
    
    return returnValue;
}
void CodeMapping::GenerateMapping(GlobalCallControlFlowGraph &gccfg)
{
    int destinationRegion = 0;
    int sourceRegion = 0;
    
    while (SPM_SIZE < totalRegionsSize)//add check for only one region.
    {
        FindMinBalancedMerge(destinationRegion, sourceRegion, gccfg);
        MergeRegions(destinationRegion, sourceRegion);
        EraseSpmRegion(sourceRegion);
    }
}
void CodeMapping::FindMinBalancedMerge(int &dst, int &src, GlobalCallControlFlowGraph &gccfg)
{
    double tempCost = 0;
    double minMergeCost = std::numeric_limits<double>::max();
    
    for (int regionOne = 1; regionOne < spmRegions; regionOne++)
    {
        for (int regionTwo = regionOne + 1; regionTwo <= spmRegions; regionTwo++)
        {
            int sizeOne = GetRegionSize(functionMapping[regionOne - 1]);
            int sizeTwo = GetRegionSize(functionMapping[regionTwo - 1]);
            int max = std::max(sizeOne, sizeTwo);
            int min = std::min(sizeOne, sizeTwo);
            
            tempCost = AlgorithmCost(regionOne, regionTwo, gccfg) * ( (max - min) / (max + min)^2 );
            if (tempCost < minMergeCost)
            {
                minMergeCost = tempCost;
                dst = regionOne;
                src = regionTwo;
            }
        }
    }
}
bool FindFunctionInRegion(std::vector<std::string> &region, std::string functionName)
{
    for (unsigned int i = 0; i < region.size(); ++i)
    {
        if (region[i].compare(functionName) == 0)
        {
            return true;
        }
    }
    return false;
}
void DepthFirstSearchGccfg(Node *node, std::vector<Node*> &trace, std::vector<std::string> &srcRegion, std::vector<std::string> &dstRegion)
{
    FunctionNode* fNode = dyn_cast<FunctionNode>(node);
    
    node->setColor(Node::GREY);
    if (
        fNode &&
        (FindFunctionInRegion(srcRegion, fNode->getMappedFunction()->getName()) ||
        FindFunctionInRegion(dstRegion, fNode->getMappedFunction()->getName()))
        )
    {
        trace.push_back(node);
    }
    else
    {
        fNode = nullptr;
    }
    for (Edge *childEdge = node->getEdges(); childEdge != nullptr; childEdge = childEdge->getNextEdge())
    {
        if (childEdge->getConnectsTo()->getColor() != Node::GREY) //Don't follow any back edges.
        {
            DepthFirstSearchGccfg(childEdge->getConnectsTo(), trace, srcRegion, dstRegion);
            if (fNode && trace.back() != node)
            {
                trace.push_back(node);
            }
        }
    }
    node->setColor(Node::BLACK);
}
std::vector<Node *> EstimateProgramTrace(std::vector<std::string> &srcRegion, std::vector<std::string> &dstRegion, GlobalCallControlFlowGraph &gccfg)
{
    std::vector<Node *>traceEstimation;
    
    gccfg.resetVisitedNodes();
    DepthFirstSearchGccfg(gccfg.getRootNode(), traceEstimation, srcRegion, dstRegion);
    
    return traceEstimation;
}
double CodeMapping::AlgorithmCost(int &regionA, int &regionB, GlobalCallControlFlowGraph &gccfg)
{
    return 0;
}
