#ifndef __GRAPH_H__
#define __GRAPH_H__

#include <fstream>
#include <list>
#include <string>
#include <vector>
#include <unordered_set>
#include <utility>

#include "llvm/Analysis/CallGraph.h"

using namespace llvm;

class Node; 
class Edge;

class Edge {
    public:
	Node *src;
	Node *dest;
	unsigned long num;

	Edge(Node *src, Node *dest, unsigned long num);
};

class Node { 
    public:
	double probability;
	std::string name;
	Node *next;
	std::list <Edge *> back_edges;

	Node(std::string name, double p);
	Node *add_next(std::string name, double p);
	Edge *add_edge_to(Node *dest, unsigned long num);
};

std::vector<CallGraphNode::CallRecord *> getExecTrace(CallGraphNode::CallRecord *);

#endif
