//
//  CodeMapping.h
//  gccfgProject
//
//  Created by Bryce Holton on 10/20/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#ifndef __gccfgProject__CodeMapping__
#define __gccfgProject__CodeMapping__

#include "GlobalCallControlFlowGraph.h"

#include <stdio.h>
#include <vector>
#include <map>
#include <string>

class CodeMapping
{
    const int SPM_SIZE;
    const std::map<std::string, int> FUNCTION_SIZES;
    
    int totalRegionsSize;
    int spmRegions;
    std::vector< std::vector<std::string> > functionMapping;
    
    int GetRegionSize(std::vector<std::string> &region);
    void MergeRegions(int &dst, int &src);
    void EraseSpmRegion(int &dst);
    
public:
    CodeMapping(int spmSize, std::map<std::string, int> fSizes);
    ~CodeMapping();
    void GenerateMapping(GlobalCallControlFlowGraph &gccfg);
    void FindMinBalancedMerge(int &dst, int &src, GlobalCallControlFlowGraph &gccfg);
    double AlgorithmCost(int &regionA, int &regionB, GlobalCallControlFlowGraph &gccfg);
};

#endif /* defined(__gccfgProject__CodeMapping__) */
