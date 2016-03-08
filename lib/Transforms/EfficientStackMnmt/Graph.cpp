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
    
using namespace llvm;

//Return all the paths iteratively from a graph rooted at the node specified and recursive functions
std::pair<std::vector<std::vector<CallGraphNode::CallRecord *> >, std::unordered_set<CallGraphNode *> > extractPaths(CallGraphNode::CallRecord *root) {
    unsigned int current_path_sel = 0; // This number always leads to next node of path that is going to be traversed
    unsigned int next_path_sel = 0; // This number always leads to the leftmost path that has not been traversed
    std::vector<std::vector<CallGraphNode::CallRecord *> > paths; // Used to keep the result
    std::unordered_set <CallGraphNode *> undecidable_cgns; // Used to keep undecidable functions
    std::queue <CallGraphNode::CallRecord *> current_path; // Used to keep a record of current path
    std::stack < std::pair< std::queue <CallGraphNode::CallRecord *>, unsigned int > > next_path; // Used to keep a record of paths that has not been completely traversed, the first element of each pair saves the nodes that have been visited, and second element indicates the next node to visit

    // Check on validity of root node
    if ((root == NULL || root->second == NULL) ) {
	errs() << "Try to generate paths for an empty graph!\n";
	exit(-1);
    }

    // Initialize the call stack
    current_path.push(root);
    int counter = 0; // This counter is used to stop the loop in case of mutual recurrsion is present
    int mutual_recursion_threshold = 500;
    while(!current_path.empty() && counter++ < mutual_recursion_threshold) { 
	// Pick up a node to visit
	CallGraphNode::CallRecord *v = current_path.back(); 

	bool only_recursive_edges = false;

	// Check if a node has only self-recursive edges
	if(v->second->size() > 0) {
	    unsigned int i;
	    for (i = 0; i < v->second->size(); i++) {
		if ((*v->second)[i] != v->second) {
		    break;
		}
	    }
	    if( i >= v->second->size())
		only_recursive_edges = true;
	}

	// Deal with endpoints - library function calls, leaf nodes, nodes with only recursive edges
	if ( (v->second->getFunction() && isLibraryFunction(v->second->getFunction())) || v->second->size() == 0 || only_recursive_edges) {
	    std::vector<CallGraphNode::CallRecord *> path;
	    // Add current path to result if the endpoint is not an inline asm
	    bool is_valid_path = true;
	    if (current_path.back()->first) {
		CallInst *call_inst = dyn_cast<CallInst>(current_path.back()->first);
		assert(call_inst);
		if (call_inst->isInlineAsm())
		    is_valid_path = false;
	    }
	    if (is_valid_path) {
		while(!current_path.empty()) {
		    path.push_back(current_path.front());
		    current_path.pop();
		}
		paths.push_back(path);
		// Keep a record if the the node is self-recursive or external
		if (only_recursive_edges || !v->second->getFunction()) {
		    undecidable_cgns.insert(v->second);
		}
	    }
	    // Go to next path that has not been completely travsed
	    if (!next_path.empty()) { 
		auto temp = next_path.top();
		next_path.pop();
		// Restore nodes that have been visited on this path
		current_path = temp.first;
		// Restore the next node to visit
		current_path_sel = temp.second;
	    }
	    // Finish current iteration
	    continue;
	}

	// If the node being visited is not an endpoint
	bool is_recursive = false;
	// Find the first non-recursursive edge of the node
	while ( current_path_sel < v->second->size()) { 
	    // Skip recursive edges
	    if ((*v->second)[current_path_sel] == v->second) {
		//undecidable_cgns.insert(v->second);
		is_recursive = true;
		current_path_sel++; 
	    }
	    else {
		break;
	    }
	}
	next_path_sel = current_path_sel + 1;

	// Decide next path to explore if there are any
	while ( next_path_sel < v->second->size()) { 
	    // Skip self-recursive edges
	    if ( (*v->second)[next_path_sel] == v->second ) {
		//undecidable_cgns.insert(v->second);
		is_recursive = true;
		next_path_sel++;
	    }
	    else { 
		// Record the next path to explore
		next_path.push(std::make_pair(current_path, next_path_sel));
		break;
	    }
	}
	//Keep a record of the found recursive node 
	if (is_recursive)
	    undecidable_cgns.insert(v->second);

	//Add selected node to current path
	unsigned int i = 0; 
	CallGraphNode::iterator cgni = v->second->begin();
	do {
	    if (i == current_path_sel) {
		current_path.push(&*cgni);
		break;
	    }
	    i++;
	    cgni++;
	} while (i < v->second->size());
	// Reset selector of next node to visit in current path
	current_path_sel = 0;
    }
    // Check the presence of mutual recursion
    if (counter >= mutual_recursion_threshold) {
	errs() << "Too many iterations, possible presence of mutual recursion\n";
	exit(-1);
    }

    return std::make_pair(paths, undecidable_cgns);
}
