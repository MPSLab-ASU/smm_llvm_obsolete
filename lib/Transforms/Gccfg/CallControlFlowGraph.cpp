//
//  CallControlFlowGraph.cpp
//  gccfgProject
//
//  Created by Bryce Holton on 8/5/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#include "CallControlFlowGraph.h"
#include "ConditionNode.h"
#include "FunctionNode.h"
#include "LoopNode.h"
#include <llvm/IR/Constants.h>
#include <llvm/IR/GlobalVariable.h>

bool CallControlFlowGraph::createConditionVertexes(std::vector<BasicBlock*> blockList)
{
    for (unsigned int i = 0; i < blockList.size(); ++i)
    {
        TerminatorInst* terminator = blockList[i]->getTerminator();
        
        if (terminator->getNumSuccessors() == 2)
        {
            ConditionNode* condition = new ConditionNode();
            condition->setMappedBlock(blockList[i]);
            addNode(condition);
        }
        else if (terminator->getNumSuccessors() > 2)
        {
            blockList[i]->print(errs());
            errs() << "This is a switch and should have been processed by this point. Fix this\n";
            return false;
        }
    }
    return true;
}
FunctionNode* buildFunctionVertex(Function* f, BasicBlock* b)
{
    FunctionNode* function = new FunctionNode();
    function->setMappedFunction(f);
    function->setMappedBlock(b);
    
    return function;
}
void CallControlFlowGraph::recursivePointerTargets(Instruction *inst, BasicBlock* block)
{
    for (User::op_iterator itr = inst->op_begin(), e = inst->op_end(); itr != e; ++itr)
    {
        if (Instruction *vi = dyn_cast<Instruction>(*itr))
        {
            // This should be recursive
            recursivePointerTargets(vi, block);
        }
        else if (Constant* ci = dyn_cast<Constant>(*itr))
        {
            if (Function* func = dyn_cast<Function>(ci))
            {
                //Function case.  This is a function to add
                addNode(buildFunctionVertex(func, block));
            }
            else if (ConstantExpr* constExp = dyn_cast<ConstantExpr>(ci))
            {
                // Constant expression case.  Could be a cast.
                if (constExp->isCast())
                {
                    if (Function* func = dyn_cast<Function>((Constant*)constExp->stripPointerCasts()))
                    {
                        FunctionNode* fNode = buildFunctionVertex(func, block);
                        fNode->setFunctionPointer(true);
                        addNode(fNode);
                    }
                }
                else
                {
                    errs() << inst->getParent()->getName() << "\n";
                    errs() << constExp->getOpcodeName() << "\n";
                    errs() << "Error: Didn't catch function pointer.  Its a constant expression w/o being cast.\n";
                }
            }
            else if (GlobalVariable* globalVar = dyn_cast<GlobalVariable>(ci))
            {
                if (ConstantArray* ca = dyn_cast<ConstantArray>(globalVar->getInitializer()))
                {
                    for (unsigned int i = 0; i < ca->getNumOperands(); ++i)
                    {
                        if (Function* func = dyn_cast<Function>(ca->getOperand(i)))
                        {
                            FunctionNode* fNode = buildFunctionVertex(func, block);
                            fNode->setFunctionPointer(true);
                            addNode(fNode);
                        }
                    }
                }
                else
                {
                    errs() << "Error: Didn't catch function pointer.  Its a global var and not an array.\n";
                }
            }
            else if (dyn_cast<ConstantInt>(ci))
            {
                // Catch the constant int case.  This is not a function pointer.
            }
            else
            {
                errs() << "Warning: This might be a function pointer, or as LLVM calls it an indirect function call.  We might not have caught the constant case.\n";
                errs() << "def const \t" << *ci << "\n";
                errs() << "Instruction \t" << *inst << "\n";
            }
        }
    }
}
bool CallControlFlowGraph::createFunctionVertexes(std::vector<BasicBlock*> blockList, unsigned int level)
{
    if (level == 1)
    {
        FunctionNode* rNode = buildFunctionVertex(blockList[0]->getParent(), &blockList[0]->getParent()->getEntryBlock());
        addNode(rNode);
        setRootNode(rNode);
    }
    for (unsigned int i = 0; i < blockList.size(); ++i)
    {
        for (BasicBlock::iterator instItr = blockList[i]->begin(); instItr != blockList[i]->end(); ++instItr)
        {
            if (CallInst* functionCall = dyn_cast<CallInst>(instItr))
            {
                Function* calledFunction = functionCall->getCalledFunction();
                if (calledFunction != NULL)
                {
                    addNode(buildFunctionVertex(calledFunction, blockList[i]));
                }
                else
                {
                    // This is a function pointer.
                    recursivePointerTargets(instItr, blockList[i]);
                }
            }
        }
    }
    return true;
}
bool CallControlFlowGraph::createLoopVertexes(LphType map)
{
    for (unsigned int i = 0; i < map.size(); ++i)
    {
        LoopNode* loop = new LoopNode();
        loop->setLoopId(map[i].second);
        loop->setMappedBlock(map[i].first);
        addNode(loop);
        if (loop->getMappedBlock()->getName().find("loop_place_holder") == std::string::npos)
        {
            setRootNode(loop);
        }
    }
    return true;
}
bool CallControlFlowGraph::createGraphVertexes(HierarchicalFlowGraph *hfg)
{
    if (!createConditionVertexes(hfg->getBlockList()))
    {
        errs() << "CCFG build error: An error occured while building condition vertexes\n";
        return false;
    }
    if (!createFunctionVertexes(hfg->getBlockList(), hfg->getLevel()))
    {
        errs() << "CCFG build error: An error occured while building function vertexes\n";
        return false;
    }
    if (!createLoopVertexes(hfg->getLphMap()))
    {
        errs() << "CCFG build error: An error occured while building loop vertexes\n";
        return false;
    }
    return true;
}
void CallControlFlowGraph::createGraphEdges()
{
    Node* node = getNodeList();
    
    while (node != NULL)
    {
        node->createEdges(this);
        node = node->getNextNode();
    }
}
bool CallControlFlowGraph::findConvergencePointsForConditionNodes()
{
    Node* node = getNodeList();
    
    while (node != NULL)
    {
        if (ConditionNode* cNode = dyn_cast<ConditionNode>(node))
        {
            if (!cNode->setConvergencePoint())
            {
                return false;
            }
        }
        node = node->getNextNode();
    }
    return true;
}
CallControlFlowGraph::CallControlFlowGraph(HierarchicalFlowGraph *hfg) : Graph()
{
    setBuildStatus(true);
    if (hfg->getBuildStatus())
    {
        if (!createGraphVertexes(hfg))
        {
            setBuildStatus(false);
        }
        else
        {
            if (!findConvergencePointsForConditionNodes())
            {
                setBuildStatus(false);
            }
            else
            {
                createGraphEdges();
            }
        }
    }
    else
    {
        setBuildStatus(false);
    }
//    printGraph();
}
CallControlFlowGraph::~CallControlFlowGraph()
{
    
}
