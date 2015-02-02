//
//  FunctionNode.h
//  gccfgProject
//
//  Created by Bryce Holton on 8/6/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#ifndef __gccfgProject__FunctionNode__
#define __gccfgProject__FunctionNode__

#include <iostream>
#include "Node.h"
#include "llvm/IR/Function.h"

class FunctionNode : public Node
{
    Function* mappedFunction;
    static int functionId;
    int localId;
    bool functionPointer;
    
public:
    FunctionNode();
    virtual ~FunctionNode();
    void setMappedFunction(Function* function){mappedFunction = function;}
    Function* getMappedFunction(){return mappedFunction;}
    virtual void print();
    void setFunctionPointer(bool fPointer){functionPointer = fPointer;};
    bool getFunctionPointer(){return functionPointer;}
    static bool classof(const Node *n) {return n->getKind() == NK_Function;}
};

#endif /* defined(__gccfgProject__FunctionNode__) */
