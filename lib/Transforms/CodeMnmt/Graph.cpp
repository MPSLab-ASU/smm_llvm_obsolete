#include <fstream>
#include <limits>
#include <queue>
#include <stack> 
#include <utility>
#include <unordered_map>
#include <unordered_set>
    
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/raw_ostream.h"
    
#include "FuncType.h"
#include "Graph.h"
    
using namespace llvm;

void dfs_visit(CallGraphNode::CallRecord *v, std::vector<CallGraphNode::CallRecord *>& exec_trace) {
    exec_trace.push_back(v);
    CallGraphNode *caller_cgn = v->second;
    for (CallGraphNode::iterator ii = caller_cgn->begin(), ie = caller_cgn->end(); ii != ie; ii++) {
	CallGraphNode::CallRecord *w = &*ii;
	CallGraphNode *called_cgn = w->second;
	Function *called_func = called_cgn->getFunction();
	// Skip library functions (consider them later?)
	if ( called_cgn->getFunction() && called_cgn != caller_cgn && !isLibraryFunction(called_func)) {
	    dfs_visit(w, exec_trace);
	    exec_trace.push_back(v);
	}
    }
}

std::vector<CallGraphNode::CallRecord *> getExecTrace(CallGraphNode::CallRecord *root) {
    std::vector<CallGraphNode::CallRecord *> exec_trace;
    dfs_visit(root, exec_trace);

    return exec_trace;
}


