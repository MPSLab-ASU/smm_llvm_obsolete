#ifndef __GRAPH_H__
#define __GRAPH_H__

#include <fstream>
#include <vector>
#include <unordered_set>
#include <utility>

#include "llvm/Analysis/CallGraph.h"

using namespace llvm;

std::pair<std::vector<std::vector<CallGraphNode::CallRecord *> >, std::unordered_set<CallGraphNode *> > extractPaths(CallGraphNode::CallRecord *);

void bfsPrint(CallGraphNode::CallRecord *, std::vector<std::vector<CallGraphNode::CallRecord *> > &paths, std::ofstream &);

#endif
