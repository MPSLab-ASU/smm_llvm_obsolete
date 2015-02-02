//
//  FunctionNode.cpp
//  gccfgProject
//
//  Created by Bryce Holton on 8/6/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#include "FunctionNode.h"

int FunctionNode::functionId = 0;

FunctionNode::FunctionNode() : Node(NK_Function)
{
    setMappedFunction(NULL);
    setFunctionPointer(false);
    localId = FunctionNode::functionId++;
}
FunctionNode::~FunctionNode()
{
    
}
void FunctionNode::print()
{
    std::string functionName = getMappedFunction()->getName();
    std::size_t found;
    while ((found = functionName.find(".")) != std::string::npos)
    {
        functionName.replace(found, 1, "_");
    }
    errs() << functionName << localId;
//    errs() << "Node" << this << "[label=\"" << getMappedFunction()->getName() << "\"]";
}
