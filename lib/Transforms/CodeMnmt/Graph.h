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

std::vector<CallGraphNode::CallRecord *> getExecTrace(CallGraphNode::CallRecord *);

#endif
