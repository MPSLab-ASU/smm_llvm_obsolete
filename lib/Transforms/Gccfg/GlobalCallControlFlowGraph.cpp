//
//  GlobalCallControlFlowGraph.cpp
//  gccfgProject
//
//  Created by Bryce Holton on 8/5/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#include "GlobalCallControlFlowGraph.h"
#include "FunctionNode.h"
#include "LoopNode.h"
#include <set>

void depthFirstSearchForLeafNodes(Node* node, std::set< std::pair<Node*, Node*> > &leafNodes)
{
    for (Edge* edgeSet = node->getEdges(); edgeSet != NULL; edgeSet = edgeSet->getNextEdge())
    {
        Node* childNode = edgeSet->getConnectsTo();
        
        if (childNode->getEdges() == NULL)
        {
            // This is a leaf node.
            if (dyn_cast<FunctionNode>(childNode) || dyn_cast<LoopNode>(childNode))
            {
                // We should be able to connect this.
                leafNodes.insert(std::make_pair(node, childNode));
            }
        }
        else
        {
            depthFirstSearchForLeafNodes(childNode, leafNodes);
        }
    }
}
void GlobalCallControlFlowGraph::buildGccfg(std::vector<CallControlFlowGraph*> graphs)
{
    std::set< std::pair<Node*, Node*> > leafNodes;
    std::set<Node*> rootsAdded;
    std::set<Node*> deleteQueue;
    
    for (unsigned int i = 0; i < graphs.size(); ++i)
    {
        //Add this graph to the list
        addNode(graphs[i]->getNodeList());
        depthFirstSearchForLeafNodes(graphs[i]->getRootNode(), leafNodes);
        // We need to replace the leafnodes with new nodes in the graph.
        for (std::set< std::pair<Node*, Node*> >::iterator leafItr = leafNodes.begin(); leafItr != leafNodes.end(); ++leafItr)
        {
            for (unsigned int j = 0; j < graphs.size(); ++j)
            {
                FunctionNode *oldFNode = NULL, *newFNode = NULL;
                LoopNode *oldLNode = NULL, *newLNode = NULL;
                
                if ( (oldFNode = dyn_cast<FunctionNode>((*leafItr).second)) && (newFNode = dyn_cast<FunctionNode>(graphs[j]->getRootNode())) )
                {
                    if (oldFNode->getMappedFunction() == newFNode->getMappedFunction())
                    {
                        if (rootsAdded.find(graphs[j]->getRootNode()) == rootsAdded.end())
                        {
                            rootsAdded.insert(graphs[j]->getRootNode());
                        }
                        replaceEdge((*leafItr).first, oldFNode, newFNode);
                        // Remove the old child Node
                        deleteQueue.insert(oldFNode);
                    }
                }
                else if ( (oldLNode = dyn_cast<LoopNode>((*leafItr).second)) && (newLNode = dyn_cast<LoopNode>(graphs[j]->getRootNode())) )
                {
                    if (oldLNode->getLoopId() == newLNode->getLoopId())
                    {
                        if (rootsAdded.find(graphs[j]->getRootNode()) == rootsAdded.end())
                        {
                            rootsAdded.insert(graphs[j]->getRootNode());
                        }
                        replaceEdge((*leafItr).first, oldLNode, newLNode);
                        // Remove the old child Node
                        deleteQueue.insert(oldLNode);
                    }
                }
            }
        }
        leafNodes.clear();
    }
    // Find Root Node for Gccfg.
    for (unsigned int i = 0; i < graphs.size(); ++i)
    {
        if (rootsAdded.find(graphs[i]->getRootNode()) == rootsAdded.end())
        {
            setRootNode(graphs[i]->getRootNode());
        }
    }
    // Delete unneeded nodes now
    for (std::set<Node*>::iterator nodeItr = deleteQueue.begin(); nodeItr != deleteQueue.end(); ++nodeItr)
    {
        deleteNode(*nodeItr);
    }
}
void GlobalCallControlFlowGraph::cleanUpGccfg(Node *node)
{
    node->setVisited(true);
    for (Edge* edgeSet = node->getEdges(); edgeSet != NULL;)
    {
        Node* child = edgeSet->getConnectsTo();
        
        if (!child->getVisited())
        {
            cleanUpGccfg(child);
        }
        if (!child->getEdges() && !dyn_cast<FunctionNode>(child))
        {
            // Remove the edge
            edgeSet = deleteEdge(node, edgeSet);
            //Remove the child node
            deleteNode(child);
        }
        else
        {
            edgeSet = edgeSet->getNextEdge();
        }
    }
}
void GlobalCallControlFlowGraph::findBackEdges(Node* node)
{
    node->setColor(Node::GREY);
    for (Edge* edgeSet = node->getEdges(); edgeSet != NULL; edgeSet = edgeSet->getNextEdge())
    {
        Node* child = edgeSet->getConnectsTo();
        
        if (child->getColor() == Node::GREY)
        {
            edgeSet->setBackEdge(true);
        }
        if (child->getColor() == Node::WHITE)
        {
            findBackEdges(child);
        }
    }
    node->setColor(Node::BLACK);
}
GlobalCallControlFlowGraph::GlobalCallControlFlowGraph(std::vector<CallControlFlowGraph*> graphs) : Graph()
{
    // Just a quick check to make sure everything is built properly before we go ahead.
    bool buildGraph = true;
    for (unsigned int i = 0; buildGraph && i < graphs.size(); i++)
    {
        if (!graphs[i]->getBuildStatus())
        {
            errs() << "ccfg not built properly, exiting gccfg build\n";
            graphs[i]->printGraph();
            buildGraph = false;
        }
    }
    if (buildGraph)
    {
        // Ok move ahead
        buildGccfg(graphs);
        resetVisitedNodes();
        cleanUpGccfg(getRootNode());
        findBackEdges(getRootNode());
        setBuildStatus(true);
    }
    else
    {
        setBuildStatus(false);
    }
}
GlobalCallControlFlowGraph::~GlobalCallControlFlowGraph()
{

}
