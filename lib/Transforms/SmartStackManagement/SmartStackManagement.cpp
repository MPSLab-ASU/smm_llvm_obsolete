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

#include <fstream>
#include <queue>
#include <tuple>
#include <stack>
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

    struct SmartStackManagementPass : public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	SmartStackManagementPass() : ModulePass(ID) {
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	// Checks whether a function is a library function (including intrinsic functions)
	inline bool isLibraryFunction(Function *func) {
	    return (func->isDeclaration()); 
	}

	// Check if a function is stack management function	
	inline bool isStackManagementFunction(Function *func) {
	    if (func->getName().count("_g2l") ==1)
		return true;
	    if (func->getName().count("_l2g") ==1)
		return true;
	    if (func->getName().count("_sstore") ==1)
		return true;
	    if (func->getName().count("_sload") ==1)
		return true;
	    if (func->getName().count("dma") ==1) {
		return true;
	    }

	    return false;
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

	virtual bool runOnModule(Module &mod) {
	    LLVMContext &context = mod.getContext();

	    // Pointer Types
	    PointerType* ptrty_int8 = PointerType::get(IntegerType::get(context, 8), 0);
	    PointerType* ptrty_ptrint8 = PointerType::get(ptrty_int8, 0);
	    // Function Types
	    std::vector<Type*> call_args;
	    call_args.push_back(ptrty_ptrint8);
	    FunctionType* functy_inline_asm = FunctionType::get(
		    Type::getVoidTy(context), // Results
		    call_args, // Params
		    false); //isVarArg

	    // External Variables
	    GlobalVariable* gvar_spm_end = new GlobalVariable(mod, // Module
		    IntegerType::get(context, 8), //Type
		    false, //isConstant
		    GlobalValue::ExternalLinkage, // Linkage
		    0, // Initializer
		    "_spm_end");

	    // Global Variables
	    GlobalVariable* gvar_mem_stack_base = mod.getGlobalVariable("_mem_stack_base");
	    GlobalVariable* gvar_spm_stack_base = mod.getGlobalVariable("_spm_stack_base");
	    GlobalVariable* gvar_spm_depth = mod.getGlobalVariable("_stack_depth");
	    GlobalVariable* gvar_stack = mod.getGlobalVariable("_stack");

	    // Functions
	    Function *func_main = mod.getFunction("main");
	    Function *func_g2l = mod.getFunction("_g2l");
	    Function *func_l2g = mod.getFunction("_l2g");
	    Function *func_sstore = mod.getFunction("_sstore");
	    Function *func_sload = mod.getFunction("_sload");

	    // Inline Assembly
	    InlineAsm *func_putSP = InlineAsm::get(functy_inline_asm, "mov $0, %rsp;", "*m,~{rsp},~{dirflag},~{fpsr},~{flags}",true);
	    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

	    // Call Graph 
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph(); // call graph
	    CallGraphNode *cgn_main = cg[mod.getFunction("main")];
	    CallGraphNode::CallRecord *root;
	    std::vector<std::vector<CallGraphNode::CallRecord *> > paths;
	    //std::unordered_set <CallGraphNode *> uncertain_functions;

	    //Step 0: extract all the paths from original call graph
	    // Initialize root node by main function
	    for (CallGraphNode::iterator cgni = cg.begin()->second->begin(), cgne = cg.begin()->second->end(); cgni != cgne; cgni++) {
		if (cgni->second == cgn_main) {
		    root = &*cgni;
		    break;
		}
	    }
	    assert(CallGraphNode::iterator(root) != cg.begin()->second->end());

	    // Extarct all the paths from call graph rooted at main function
	    auto res = extractPaths(root);
	    paths = res.first;
	    /*
	    // Print out all the paths
	    for (size_t i = 0; i < paths.size(); i++) {
	    for (size_t j = 0; j < paths[i].size(); j++) {
	    if (paths[i][j]->second->getFunction())
	    errs() << paths[i][j]->first << " " << paths[i][j]->second->getFunction()->getName() << "\t";
	    else
	    errs() << paths[i][j]->first << " " << "externalNode" << "\t";
	    }
	    errs() << "\n";
	    }
	    errs() << "\n\n";
	     */

	    /*
	    // Step 1 : Add noinline attributes to functions
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		if (fi->hasFnAttribute(Attribute::NoInline) || fi->hasFnAttribute(Attribute::AlwaysInline) )
		    continue;
		fi->addFnAttr(Attribute::NoInline);
	    }
	    */

	    // Step 2: Insert g2l function calls
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		//errs() << fi->getName() << "\n";
		Function *caller = &*fi;
		// Skip library functions
		if (isLibraryFunction(caller))
		    continue;
		// Skip stack management functions
		if (isStackManagementFunction(caller))
		    continue;
		// Skip main function
		if (&*fi == func_main)
		    continue;
		// Process user-defined functions
		for (Function::arg_iterator ai = fi->arg_begin(), ae = fi->arg_end(); ai != ae; ai++) {
		    // Find user instructions of pointer arguments and replace the uses with the result of calling g2l on the arguments
		    if (ai->getType()->isPointerTy()) { 
			//errs() << "\t" << ai->getName() << " : " << *ai->getType() << "\n";
			for (Value::user_iterator ui = ai->user_begin(), ue = ai->user_end(); ui != ue; ++ui) {
			    if (Instruction *user_inst = dyn_cast<Instruction>(*ui)) { 
				//errs() << "\t\t" << *user_inst << "\n";
				// If the user instruction a phi instruction, insert g2l function on the incoming basic blocks
				if (PHINode *target = dyn_cast<PHINode>(user_inst)) {
				    for (unsigned int i = 0; i < target->getNumIncomingValues(); i++) {
					if(target->getIncomingValue(i) == ai) { 
					    IRBuilder<> builder(target->getIncomingBlock(i)->getTerminator()); // Instruction will be inserted before this instruction
					    // Cast the value (in this case, a memory address) to be of char pointer type required by g2l function
					    Value *cast_to = builder.CreatePointerCast(ai, Type::getInt8PtrTy(context), "cast_to_char_pointer"); 
					    // Call the function l2g with the value with cast type
					    Value *call_g2l = builder.CreateCall(func_g2l, cast_to, "g2l_on_char_pointer");
					    // Cast the result back to be of the original type
					    Value *cast_from = builder.CreatePointerCast(call_g2l, ai->getType(), "cast_from_result");
					    // Replace the use of pointer argument (At most one use in phi instruction)
					    target->setOperand(i, cast_from);
					}

				    }
				} else { // If the user instruction is not a phi instruction, insert g2l function before it
				    IRBuilder<> builder(user_inst); // Instruction will be inserted before this instruction
				    // Cast the value (in this case, a memory address) to be of char pointer type required by g2l function
				    Value *cast_to = builder.CreatePointerCast(ai, Type::getInt8PtrTy(context), "cast_to_char_pointer");
				    // Call the function l2g with the value with cast type
				    Value *call_g2l = builder.CreateCall(func_g2l, cast_to, "g2l_on_char_pointer");
				    // Cast the result back to be of the original type
				    Value *cast_from = builder.CreatePointerCast(call_g2l, ai->getType(), "cast_from_result"); 
				    // Replace the uses of the pointer argument
				    for (unsigned int i = 0; i < user_inst->getNumOperands(); i++) {
					if (user_inst->getOperand(i) == ai ) 
					    user_inst->setOperand(i, cast_from); 
				    }
				}
			    }
			}
		    }
		}
	    }

	    // Step 3: Insert l2g functions
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		//errs() << fi->getName() << "\n";
		Function *caller = &*fi;
		// Skip library functions
		if (isLibraryFunction(caller))
		    continue;
		// Skip stack management functions
		if (isStackManagementFunction(caller))
		    continue;
		// Process user-defined functions
		for (Function::iterator bi = fi->begin(), be = fi->end(); bi != be; ++bi) {
		    for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ii++) {
			Instruction *inst = ii;
			if (CallInst *call_func = dyn_cast<CallInst>(inst)) {
			    // Skip inline assembly
			    if (call_func->isInlineAsm())
				continue;
			    Function *callee = call_func->getCalledFunction();
			    // If the called function is a function pointer or if it is not a stack management or an intrinsic function, go ahead and process
			    if (callee) { 
				if (isStackManagementFunction(callee))
				    continue;
				if (callee->isIntrinsic())
				    continue;
			    } 
			    //  Insert l2g function before function calls wth address arguments
			    for (unsigned int i = 0, n = call_func->getNumArgOperands(); i < n; i++) { 
				Value *operand = call_func->getArgOperand(i);
				if (operand->getType()->isPointerTy() ) {
				    IRBuilder<> builder(call_func); // Instruction will be inserted before ii
				    // Cast the value (in this case, a memory address) to be of char pointer type required by l2g function
				    Value *cast_to = builder.CreatePointerCast(operand, Type::getInt8PtrTy(context), "cast_to_char_pointer"); 
				    // Call the function l2g with the value with cast type
				    Value *call_l2g = builder.CreateCall(func_l2g, cast_to, "l2g_on_char_pointer"); 
				    // Cast the result back to be of the original type
				    Value *cast_from = builder.CreatePointerCast(call_l2g, operand->getType(), "cast_from_result"); 
				    for (unsigned int i = 0; i < call_func->getNumOperands(); i++) {
					// Replace the use of the original memory address with the translated address
					if (call_func->getOperand(i) == operand ) 
					    // Replace the use of the original memory address with the translated address
					    call_func->setOperand(i, cast_from); 
				    }
				}
			    }

			}
		    }
		}
	    }

	    // Step 4: Insert management functions
	    std::vector <std::tuple<long, long, std::string> > cuts;
	    // Read SSDM output
	    std::ifstream ifs;
	    ifs.open("wcg_cuts.txt", std::fstream::in);
	    assert(ifs.good());
	    // Read function stack sizes
	    while (ifs.good()) {
		long i, j;
		std::string func_name;
		ifs >> i >> j >> func_name;
		cuts.push_back(std::make_tuple(i-1, j-1, func_name));
	    }
	    ifs.close();


	    // Insert stack management functions according to SSDM output
	    for (size_t ci = 0; ci < cuts.size(); ci++) {
		long i, j;
		std::string func_name;
		i = std::get<0>(cuts[ci]);
		j = std::get<1>(cuts[ci]);
		func_name = std::get<2>(cuts[ci]);
		assert(paths[i][j]->first && paths[i][j]->second);
		Instruction *inst = dyn_cast<Instruction> (paths[i][j]->first);
		//CallGraphNode *called_cgn = dyn_cast<CallGraphNode> (paths[i][j]->second);

		//errs() << "Inserting cuts: ";
		//errs() << i << " " << j << " " << *paths[i][j]->first << " " << paths[i][j]->second->getFunction()->getName() << "\n";

		BasicBlock::iterator ii(inst);
		// Check if stack management functions have been inserted
		BasicBlock::iterator pos = ii;
		long k = 0;
		do {
		    if (pos == ii->getParent()->begin())
			break;
		    pos--;
		    k++;
		} while(k < 2);

		if (k >= 2) {
		    CallInst *call_inst = dyn_cast<CallInst>(pos);
		    if (call_inst && call_inst->getCalledFunction() == func_sstore)
			continue;
		}


		Instruction *next_inst = &*(++ii);
		CallInst *call_func = dyn_cast<CallInst>(inst);
		assert(call_func);

		// Before the function call
		// Insert a sstore function
		CallInst::Create(func_sstore, "", inst);
		// Insert putSP(_spm_stack_base)
		CallInst::Create(func_putSP, gvar_spm_stack_base, "", inst);
		// After the function call
		// Read value of _stack_depth after the function call
		LoadInst* val__spm_depth = new LoadInst(gvar_spm_depth, "", false, next_inst);
		ConstantInt* const_int32_0 = ConstantInt::get(context, APInt(32, StringRef("0"), 10));
		ConstantInt* const_int64_1 = ConstantInt::get(context, APInt(64, StringRef("1"), 10));
		// Calculate _stack_depth - 1
		BinaryOperator* val__spm_depth1 = BinaryOperator::Create(Instruction::Sub, val__spm_depth, const_int64_1, "sub", next_inst);
		// Get the address of _stack[_stack_depth-1]
		std::vector<Value*> ptr_arrayidx_indices;
		ptr_arrayidx_indices.push_back(const_int32_0);
		ptr_arrayidx_indices.push_back(val__spm_depth1);
		Instruction* ptr_arrayidx = GetElementPtrInst::Create(gvar_stack, ptr_arrayidx_indices, "arrayidx", next_inst);
		// Get the address of _stack[_stack_depth-1].spm_address
		std::vector<Value*> ptr_spm_addr_indices;
		ptr_spm_addr_indices.push_back(const_int32_0);
		ptr_spm_addr_indices.push_back(const_int32_0);
		Instruction* ptr_spm_addr = GetElementPtrInst::Create(ptr_arrayidx, ptr_spm_addr_indices, "spm_addr", next_inst);
		// Insert putSP(_stack[_stack_depth-1].spm_addr)
		CallInst::Create(func_putSP, ptr_spm_addr, "", next_inst);
		// Insert a corresponding sload function
		CallInst::Create(func_sload, "", next_inst);

		// Check if the function has return value
		Type * retty = call_func->getType();
		if (retty->isVoidTy())
		    continue;
		// Save return value in a global variable temporarily until sload is executed if it is used
		GlobalVariable *gvar = NULL; // Always create a new global variable in case of recursive functions

		for (Value::user_iterator ui_ret = call_func->user_begin(), ue_ret = call_func->user_end(); ui_ret != ue_ret; ++ui_ret) {
		    if (Instruction *user_inst = dyn_cast<Instruction>(*ui_ret)) { // We have found the use of return value
			if (!gvar) {
			    gvar = new GlobalVariable(mod, //Module
				    retty, //Type
				    false, //isConstant
				    GlobalValue::ExternalLinkage, //linkage
				    0, // Initializer
				    "_gvar"); //Name
			    // Initialize the temporary global variable
			    gvar->setInitializer(Constant::getNullValue(retty));
			    // Save return value to the global variable before sload is called
			    StoreInst *st_ret = new StoreInst(call_func, gvar);
			    st_ret->insertAfter(call_func);
			}

			if (PHINode *target = dyn_cast<PHINode>(user_inst)) { // Return value is used in a phi instruction
			    //errs() << *target << "\n";
			    for (unsigned int i = 0; i < target->getNumIncomingValues(); i++) {
				if(target->getIncomingValue(i) == call_func) {
				    // Read the global variable
				    LoadInst *restore_ret = new LoadInst(gvar, "", target->getIncomingBlock(i)->getTerminator());
				    // Find the use of return value and replace it (At most one use in phi instruction)
				    target->setOperand(i, restore_ret);
				}

			    }
			} else { // Return value is used in a non-phi instruction
			    // Read the global variable
			    LoadInst *restore_ret = new LoadInst(gvar, "", user_inst);
			    // Find the uses of return value and replace them
			    for (unsigned int i = 0; i < user_inst->getNumOperands(); i++) {
				if (user_inst->getOperand(i) == call_func) { 
				    user_inst->setOperand(i, restore_ret);
				}
			    }
			}
		    }
		}
	    }

	    /*
	    // Print out all the paths
	    for (size_t i = 0; i < paths.size(); i++) {
		for (size_t j = 0; j < paths[i].size(); j++) {
		    if (paths[i][j]->second->getFunction())
			errs() << paths[i][j]->first << " " << paths[i][j]->second->getFunction()->getName() << "\t";
		    else
			errs() << paths[i][j]->first << " " << "externalNode" << "\t";
		}
		errs() << "\n";
	    }*/

	    // Step 5: transform the main function to an user-defined function
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
		    if (dyn_cast<CallInst>(inst)) {
			CallInst::Create(func_getSP, gvar_mem_stack_base, "", inst);
			new StoreInst(gvar_spm_end, gvar_spm_stack_base, "", inst);
			CallInst::Create(func_putSP, gvar_spm_stack_base, "", inst); 
		    }
		    else if (inst->getOpcode() == Instruction::Ret) {
			CallInst::Create(func_putSP, gvar_mem_stack_base, "", inst); 
		    }
		}
	    }



	    return true;
	}
    };
}

char SmartStackManagementPass::ID = 0; //Id the pass.
static RegisterPass<SmartStackManagementPass> X("smmssm", "Smart Stack Management Pass"); //Register the pass.

