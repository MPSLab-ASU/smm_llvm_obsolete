//===- --------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements several methods that are used to extract functions,
// loops, or portions of a module from the rest of the module.
//
//===----------------------------------------------------------------------===//

#include <iostream>
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
#include "llvm/IR/Attributes.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Support/raw_ostream.h"


using namespace llvm;

namespace {


    struct StackManagementHelperPass : public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	StackManagementHelperPass() : ModulePass(ID) {
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	// Checks whether a function is a library function (including intrinsic functions)
	inline bool isLibraryFunction(Function *func) {
	    return (func->isDeclaration()); 
	}

	// Check if a function is stack management helper function	
	inline bool isStackManagementHelperFunction(Function *func) {
	    if (func->getName().count("_get_func_stack_size") == 1)
		return true;
	    if (func->getName().count("_dump_func_stack_sizes") == 1)
		return true;
	    return false;
	}

	// Instrument the program specified by mod with stack management helper functions that will collect the stack size of each function
	bool getWcgNodeWeights(Module &mod) {
	    LLVMContext &context = mod.getContext();

	    // Types
	    PointerType* ptrty_int8 = PointerType::get(IntegerType::get(context, 8), 0);
	    PointerType* ptrty_ptrint8 = PointerType::get(ptrty_int8, 0);

	    ArrayType* arrayty_format = ArrayType::get(IntegerType::get(context, 8), 4);

	    std::vector<Type*> call_args;
	    call_args.push_back(ptrty_ptrint8);
	    FunctionType* functy_inline_asm = FunctionType::get(
		    Type::getVoidTy(context), // Results
		    call_args, // Params
		    false); //isVarArg


	    // Global variables
	    GlobalVariable* gvar_sp_calling = mod.getGlobalVariable("_sp_calling");
	    assert(gvar_sp_calling);
	    GlobalVariable* gvar_func_name = mod.getGlobalVariable("_func_name");
	    assert(gvar_func_name);
	    GlobalVariable* gvar_format = new GlobalVariable(/*Module=*/mod,
		    /*Type=*/arrayty_format,
		    /*isConstant=*/true,
		    /*Linkage=*/GlobalValue::PrivateLinkage,
		    /*Initializer=*/0, // has initializer, specified below
		    /*Name=*/".str_format");

	    // Functions
	    Function *func_main = mod.getFunction("main");
	    Function *func_get_func_stack_size = mod.getFunction("_get_func_stack_size");
	    Function *func_dump_func_stack_sizes = mod.getFunction("_dump_func_stack_sizes");

	    // Inline assembly
	    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

	    // Const values
	    Constant *const_format = ConstantDataArray::getString(context, "%s ", true);
	    ConstantInt* const_int64_0 = ConstantInt::get(context, APInt(64, StringRef("0"), 10));

	    // Initialize the global variable which saves format string
	    gvar_format->setInitializer(const_format);

	    // Get the pointer to the global variable which saves format string
	    std::vector<Constant*> const_ptr_indices;
	    const_ptr_indices.push_back(const_int64_0);
	    const_ptr_indices.push_back(const_int64_0);
	    Constant* const_ptr_format = ConstantExpr::getGetElementPtr(gvar_format, const_ptr_indices);

	    // Step 0: transform the main function to an user-defined function
	    // Create an external function called smm_main
	    Function *func_smm_main = Function::Create(cast<FunctionType>(func_main->getType()->getElementType()), func_main->getLinkage(), "smm_main", &mod);
	    ValueToValueMapTy VMap;
	    std::vector<Value*> args;

	    // Set up the mapping between arguments of main to those of smm_main
	    Function::arg_iterator ai_new = func_smm_main->arg_begin();
	    for (Function::arg_iterator ai = func_main->arg_begin(), ae = func_main->arg_end(); ai != ae; ++ai) { 
		ai_new->setName(ai->getName());
		VMap[ai] = ai_new;
		args.push_back(ai);
		ai_new++;
	    }
	    // Copy the function body from main to smm_main
	    SmallVector<ReturnInst*, 8> Returns;
	    CloneFunctionInto(func_smm_main, func_main, VMap, true, Returns);

	    // Delete all the basic blocks in main function
	    std::vector<BasicBlock*> bb_list;
	    for (Function::iterator bi = func_main->begin(), be = func_main->end();  bi!= be; ++bi) { 
		for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ++ii) {
		    ii->dropAllReferences(); //Make sure there are no uses of any instruction
		} 
		bb_list.push_back(bi);
	    }
	    for (unsigned int i = 0; i < bb_list.size(); ++i) {
		bb_list[i]->eraseFromParent();
	    }

	    // Create the new body of main function which calls smm_main and return 0
	    BasicBlock* entry_block = BasicBlock::Create(getGlobalContext(), "EntryBlock", func_main);
	    IRBuilder<> builder(entry_block);
	    builder.CreateCall(func_smm_main, args);
	    Value *zero = builder.getInt32(0);
	    builder.CreateRet(zero);

	    // Insert starting and ending code in main function
	    for (Function::iterator bi = func_main->begin(), be = func_main->end(); bi != be; ++bi) {
		for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ii++) {
		    Instruction *inst  = &*ii;
		    if (inst->getOpcode() == Instruction::Ret) {
			CallInst::Create(func_dump_func_stack_sizes, "", inst);
		    }
		}
	    }

	    // Step 1 : Add noinline attributes to functions
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		//errs() << fi->getName() << "\n";
		if (fi->hasFnAttribute(Attribute::NoInline) || fi->hasFnAttribute(Attribute::AlwaysInline) )
		    continue;
		fi->addFnAttr(Attribute::NoInline);
	    }

	    // Step 2: Insert management helper functions
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		Function *caller = &*fi;
		//Skip if current function is a library function
		if (isLibraryFunction(caller))
		    continue;

		// Skip if current function is a stackmanagement helper function
		if (isStackManagementHelperFunction(caller))
		    continue;

		// If current function is an user-defined function

		// Get or build a gloabal variable which saves the name of current function
		GlobalVariable* gvar_curfuncname = mod.getGlobalVariable("__func__." + fi->getName().str(), true);
		Constant* const_ptr_curfuncname; 
		if (!gvar_curfuncname) {
		    //errs() << "__func__." + fi->getName().str() << "\n";
		    ArrayType* arrayty_curfuncname =ArrayType::get(IntegerType::get(context, 8), fi->getName().size()+1);
		    Constant *const_curfuncname = ConstantDataArray::getString(context, fi->getName(), true);
		    gvar_curfuncname = new GlobalVariable(/*Module=*/mod,
			    /*Type=*/arrayty_curfuncname,
			    /*isConstant=*/true,
			    /*Linkage=*/GlobalValue::PrivateLinkage,
			    /*Initializer=*/0, // has initializer, specified below
			    /*Name=*/"__func__." + fi->getName());
		    gvar_curfuncname->setAlignment(1);
		    const_ptr_curfuncname = ConstantExpr::getGetElementPtr(gvar_curfuncname, const_ptr_indices);
		    gvar_curfuncname->setInitializer(const_curfuncname);
		}
		else
		    const_ptr_curfuncname = ConstantExpr::getGetElementPtr(gvar_curfuncname, const_ptr_indices);

		// Set up arguments for printf
		std::vector<Value*> call_params;
		call_params.push_back(const_ptr_format);
		call_params.push_back(const_ptr_curfuncname);

		if (! (&*fi == func_main) ) {
		    // Insert a printf function call to print out the caller's name
		    Instruction *firstNonPhiInst = fi->begin()->getFirstNonPHI();
		    new StoreInst(const_ptr_curfuncname, gvar_func_name, false, firstNonPhiInst);
		    // Insert _get_stack_size() function before the first non-ph instruction
		    CallInst::Create(func_get_func_stack_size, "", firstNonPhiInst);
		}

		for (inst_iterator ii = inst_begin(fi), ie = inst_end(fi); ii != ie; ii++) {
		    Instruction *inst = &*ii;
		    // If we find a function call, read the current SP value and print out the caller's name
		    if (CallInst * call_func = dyn_cast<CallInst>(inst)) {
			// Skip if callee is an inline asm
			if (call_func->isInlineAsm())
			    continue;
			Function *callee = call_func->getCalledFunction();
			// SKip if callee is a function pointer or a library function
			if(!callee) 
			    continue;
			if( isLibraryFunction(callee)) 
			    continue;
			if( isStackManagementHelperFunction(callee)) 
			    continue;
			// Read the current SP value
			CallInst::Create(func_getSP, gvar_sp_calling, "", call_func);
		    }
		}
	    }
	    return true;
	}

	//Return all the paths iteratively from a graph rooted at the node specified and recursive functions
	std::pair<std::vector<std::vector<CallGraphNode::CallRecord *> >, std::unordered_set<CallGraphNode *> > extractPaths(CallGraphNode::CallRecord *root) {
	    unsigned int current_path_sel = 0; // This number always leads to next node of path that is going to be travsed
	    unsigned int next_path_sel = 0; // This number always leads to the leftmost path that has not been travsed
	    std::vector<std::vector<CallGraphNode::CallRecord *> > paths; // Used to keep the result
	    std::unordered_set <CallGraphNode *> uncertain_functions; // Used to keep uncertain functions
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
			CallInst *call_func = dyn_cast<CallInst>(current_path.back()->first);
			assert(call_func);
			if (call_func->isInlineAsm())
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
			    uncertain_functions.insert(v->second);
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
			//uncertain_functions.insert(v->second);
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
			//uncertain_functions.insert(v->second);
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
		    uncertain_functions.insert(v->second);

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

	    return std::make_pair(paths, uncertain_functions);
	}


	// Visit the graph rooted at ROOT in a BFS manner iteratively and print out path ID  for each edge
	void bfsPrint(CallGraphNode::CallRecord *root, std::vector<std::vector<CallGraphNode::CallRecord *> > &paths, std::ofstream &ofs) {
	    std::queue <CallGraphNode::CallRecord *> q; // Used to keep nodes to visit
	    std::unordered_set <CallGraphNode::CallRecord *> labels; // Used to keep a record on nodes which have been visited
	    q.push(root);
	    labels.insert(root);
	    while(!q.empty()) {
		// Dequeue a node v
		CallGraphNode::CallRecord *v = q.front();
		q.pop();
		/*
		   if (v->second->getFunction())
		   errs() << v->second->getFunction()->getName();
		   else 
		   errs() << "externalNode";
		   errs() << "\n";
		 */
			    
		// Visit all the neighbours of v that have not been visited
		for (CallGraphNode::iterator cgni = v->second->begin(), cgne = v->second->end(); cgni != cgne; cgni++) {
		    //Find a neighbour node w of v
		    CallGraphNode::CallRecord *w = &*cgni;
		    // If w has not been labeled, insert it to the queue and label it
		    if (labels.find(w) == labels.end()) {
			q.push(w); 
			labels.insert(w);
		    }
		    // Find and print out the path ID for v->w edge
		    for (size_t i = 0; i < paths.size(); i++) {
			for (size_t j = 0; j < paths[i].size() - 1; j++) {
			    if ( (v == paths[i][j]) && (w == paths[i][j+1])) {
				if (v->second->getFunction())
				    ofs << v->second->getFunction()->getName().str();
				else 
				    ofs << "externalNode";
				ofs << " ";
				if (w->second->getFunction())
				    ofs << w->second->getFunction()->getName().str();
				else 
				    ofs << "externalNode";
				ofs << " " << i+1 << "\n";
			    }
			}
		    }
		}
	    }
	}

	bool extractAnnotatedWcgPaths(Module &mod) {
	    long ssize;
	    std::string func_name;
	    std::ofstream ofs;
	    std::ifstream ifs;
	    std::unordered_map <std::string, long> wcg_nodes;
	    std::vector<std::vector<CallGraphNode::CallRecord *> > paths;
	    std::unordered_set <CallGraphNode *> uncertain_functions;
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph(); // call graph
	    CallGraphNode *cgn_main = cg[mod.getFunction("main")]; 
	    CallGraphNode::CallRecord *root;


	    // Initialize root node by main function
	    for (CallGraphNode::iterator cgni = cg.begin()->second->begin(), cgne = cg.begin()->second->end(); cgni != cgne; cgni++) {
		if (cgni->second == cgn_main) {
		    root = &*cgni;
		    break;
		}
	    }
	    assert(CallGraphNode::iterator(root) != cg.begin()->second->end());

	    // Get all the paths from the call graph rooted at main
	    auto res = extractPaths(root); 
	    paths = res.first;
	    uncertain_functions = res.second;

	    ifs.open("wcg_nodes.txt", std::fstream::in);
	    // Read function stack sizes
	    while (ifs.good()) {
		ifs >> func_name >> ssize;
		wcg_nodes[func_name]  = ssize;
	    }

	    /*
	    for (auto ii = wcg_nodes.begin(), ie = wcg_nodes.end(); ii != ie; ii++) {
		errs() << ii->first << " " << ii->second << "\n";
	    }
	    */

	    // Print out all the edges
	    ofs.open("wcg_paths.txt", std::fstream::out) ;
	    bfsPrint(root, paths, ofs);

	    ofs << "#\n";

	    // Print out annotated WCG paths
	    for (size_t i = 0; i < paths.size(); i++) {
		//ofs << "path" << i << " : ";
		for (size_t j = 0; j < paths[i].size(); j++) {
		    if (paths[i][j]->second->getFunction()) {
			std::string func_name = paths[i][j]->second->getFunction()->getName().str();
			// Print node name (function name)
			ofs << func_name << " ";
			// Print node weight (function stack size)
			if (wcg_nodes.find(func_name) != wcg_nodes.end())
			    ofs << wcg_nodes[func_name];
			else {
			    // TODO Get library function stack sizes
			    //errs() << func_name << "\n";
			    ofs << std::numeric_limits<short>::max();
			}
			ofs << " ";
			// Print edge weight (number of function calls)
			if (j < paths[i].size()-1)
			    ofs << "1";
			else
			    ofs << "0";
			ofs << " ";
		    }
		    else {
			ofs << "externalNode 0 ";
		    }
		}
		ofs << "\n";
	    }

	    ofs << "#\n";

	    // Print out uncertain function names
	    for (auto ii = uncertain_functions.begin(), ie = uncertain_functions.end(); ii != ie; ii++) {
		if ((*ii)->getFunction()) {
		    ofs << (*ii)->getFunction()->getName().str() << "\n";
		}
		else 
		    ofs << "externalNode\n";
	    }

	    ofs.close();
	    ifs.close();

	    return false;
	}

	virtual bool runOnModule(Module &mod) {
	    std::ifstream ifs;
	    ifs.open("wcg_nodes.txt", std::fstream::in);
	    if (!ifs.good()) {
		errs() << "Dumping node weights of WCG to wcg_nodes.txt...\n";
		ifs.close();
		getWcgNodeWeights(mod);
	    }
	    else {
		errs() << "Dumping annotated paths of WCG to wcg_paths.txt...\n";
		ifs.close();
		extractAnnotatedWcgPaths(mod);
	    }
	    return true;
	}
    };
}

char StackManagementHelperPass::ID = 0; //Id the pass.
static RegisterPass<StackManagementHelperPass> X("smmsmh", "Stack Management Helper Pass"); //Register the pass.

