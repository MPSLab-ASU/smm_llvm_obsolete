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

#include <fstream>
#include <queue>
#include <tuple>
#include <stack>
#include <utility>
#include <unordered_map>
#include <unordered_set>

#include "definition.h"
#include "instrumentation.h"
#include "graph.h"
#include "function.h"
#define DEBUG

using namespace llvm;

namespace {

    struct SmartStackManagementPass : public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	SmartStackManagementPass() : ModulePass(ID) {
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
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

	    // Functions
	    Function *func_main = mod.getFunction("main");
	    Function *func_l2g = mod.getFunction("_l2g");
	    Function *func_sstore = mod.getFunction("_sstore");

	    // Inline Assembly
	    InlineAsm *func_putSP = InlineAsm::get(functy_inline_asm, "mov $0, %rsp;", "*m,~{rsp},~{dirflag},~{fpsr},~{flags}",true);
	    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

	    // Call Graph 
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph(); // call graph
	    CallGraphNode *cgn_main = cg[mod.getFunction("main")];
	    CallGraphNode::CallRecord *root;
	    std::vector<std::vector<CallGraphNode::CallRecord *> > paths;
	    std::unordered_set <CallGraphNode *> undecidable_cgns;

	    //Step 0: extract all the paths from call graph root at main function
	    // Initialize root node by main function
	    for (CallGraphNode::iterator cgni = cg.begin()->second->begin(), cgne = cg.begin()->second->end(); cgni != cgne; cgni++) {
		if (cgni->second == cgn_main) {
		    root = &*cgni;
		    break;
		}
	    }
	    assert(CallGraphNode::iterator(root) != cg.begin()->second->end());
	    // Extarct paths 
	    auto res = extractPaths(root);
	    paths = res.first;
	    undecidable_cgns = res.second;

	    // Step 1: get SSMD cuts
	    std::unordered_map <unsigned, std::vector <std::pair<unsigned, std::string> > > cuts;
	    // Read SSDM output file
	    std::ifstream ifs;
	    ifs.open("wcg_cuts.txt", std::fstream::in);
	    assert(ifs.good());
	    // Read function stack sizes
#ifdef DEBUG
	    errs() << "Reading SSDM output file...\n";
	    errs() << "{\n";
#endif
	    while (ifs.good()) {
		unsigned i, j;
		std::string func_name;
		ifs >> i >> j >> func_name;
		// Ignore white spaces after the last line
		if (func_name != "") {
#ifdef DEBUG		    
		    errs() << "\t" << i << " " << j << " " << func_name << "\n";
#endif
		    cuts[i-1].push_back( std::make_pair(j-1, func_name) );
		}
	    }
	    ifs.close();
#ifdef DEBUG
	    errs() << "}\n\n\n";
	    errs() << "Sorting SSDM cuts according to paths...\n";
	    errs() << "{\n";
#endif

	    // Sort cuts acoording to paths
	    for (auto cutsi = cuts.begin(), cutse = cuts.end(); cutsi != cutse; cutsi++) {
		std::sort(cutsi->second.begin(), cutsi->second.end());
#ifdef DEBUG
		errs() << "\tpath " << cutsi->first << " : ";
		for (size_t i = 0; i < cutsi->second.size(); i++) 
		    errs() << cutsi->second[i].first << " " << cutsi->second[i].second << "  ";
		errs() << "\n";
#endif
	    }
#ifdef DEBUG
	    errs() << "}\n\n\n";
#endif

	    // Step 2: Decide the instrument points for l2g and g2l functions
	    std::unordered_map <CallInst *, std::unordered_set<unsigned> > l2g_insert_pts;
	    std::unordered_map <Function *, std::vector<CallInst *> > refs; // Call sites of functions
	    // Get references of user-defined functions with pointer-type arguments
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		if(CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second)) {
		    // Skip external nodes
		    if(!cgn->getFunction())
			continue;
		    // Skip library functions
		    if (isLibraryFunction(cgn->getFunction()))
			continue;
		    // Skip management functions
		    if (isStackManagementFunction(cgn->getFunction()))
			continue;

		    // Process user-defined functions
		    for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
			CallInst *call_inst = dyn_cast <CallInst> (cgni->first);
			CallGraphNode *called_cgn = dyn_cast <CallGraphNode> (cgni->second);
			Function *callee = called_cgn->getFunction();
			assert(call_inst && called_cgn);
			// Skip inline assembly
			if (call_inst->isInlineAsm())
			    continue;
			if (callee) {
			    // Skip calls to management functions
			    if(isStackManagementFunction(callee))
				continue;
			    // Skip recursive edges
			    if (cgn == called_cgn) 
				continue;

			}
			// Call instructions to all the external nodes will be mapped to the NULL key
			refs[callee].push_back(call_inst);
		    }
		}
	    }

#ifdef DEBUG
	    errs() << "References of functions:\n";
	    errs() << "{\n";
	    //std::unordered_map <Function *, std::vector<CallInst *> > refs; // Call sites of functions
	    for (auto ii = refs.begin(), ie = refs.end(); ii != ie; ii++) {
		if (ii->first)
		    errs() << "\t" << ii->first->getName() << "\n";
		else 
		    errs() << "\texternalNode\n";
		for (size_t i = 0; i < ii->second.size(); i++) {

		    errs() << "\t\t" << ii->second[i]->getParent()->getParent()->getName() << "  (" <<*ii->second[i] << ")\n";
		}
	    }
	    errs() << "}\n\n\n";
	    errs() << "Definitions of pointer-type arguments\n";
	    errs() << "{\n";
#endif

	    // Decide l2g insert points
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		if(CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second)) {
		    // Skip external nodes
		    if(!cgn->getFunction()) 
			continue;
		    // Skip library functions
		    if (isLibraryFunction(cgn->getFunction()))
			continue;
		    // Skip management functions
		    if (isStackManagementFunction(cgn->getFunction()))
			continue;
#ifdef DEBUG
		    errs() << "\t" << cgn->getFunction()->getName() << "\n";
#endif
		    // Process user-defined functions
		    for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
			CallInst *call_inst = dyn_cast <CallInst> (cgni->first);
			CallGraphNode *called_cgn = dyn_cast <CallGraphNode> (cgni->second);
			Function *callee = called_cgn->getFunction();
			assert(call_inst && called_cgn);
			// Skip inline assembly
			if (call_inst->isInlineAsm())
			    continue;
			if (callee) {
			    // Skip calls to management functions
			    if(isStackManagementFunction(callee))
				continue;
			}

#ifdef DEBUG
			errs() << "\t\t" << *call_inst << "\n";
#endif
			// Get all the possible definitions of pointer-type arguments TODO: function pointers need to be considered
			for (unsigned arg_index = 0; arg_index < call_inst->getNumArgOperands(); arg_index++) {
			    Value *val = call_inst->getArgOperand(arg_index);
			    if ( val->getType()->isPointerTy() ) {
#ifdef DEBUG
				errs() << "\t\t\t" << *val << "\n";
#endif
				// Get the definitions of the pointer-type argument being processed
				auto defs = getDefs(val, refs);

#ifdef DEBUG
				auto res = defs;
				for (unsigned i = 0; i < res.size(); i++) {
				    errs() << "\t\t\t\t(" << *res[i].first << ") ";
				    if (res[i].second == DATA)
					errs() << " uses global data\n";
				    else if (res[i].second == HEAP)
					errs() << " uses heap data\n";
				    else if (res[i].second == STACK) {
					Instruction *inst = dyn_cast<Instruction>(res[i].first);
					assert(inst);
					errs() << " uses stack data defined in function " << inst->getParent()->getParent()->getName() << "\n";
				    }
				    else if (res[i].second == UNDEF)
					errs() << " uses UNDEF data\n";
				    else
					errs() << " errors\n";
				}
#endif

				// Check if any definition of the argument is in stack segment or undecided
				size_t k;
				for (k = 0; k < defs.size() ; k++ ) {
				    if (defs[k].second == STACK || defs[k].second == UNDEF) 
					break;
				}
				// Skip the argument if none of its definitions could be in stack segment
				if (k >= defs.size())
				    continue;

				// Check if the call happens at a cut 
				for (size_t i = 0; i < paths.size(); i++) {
				    for (size_t j = 0; j < paths[i].size(); j++) {
					if (paths[i][j]->first == cgni->first) {
					    for (size_t k = 0; k < cuts[i].size(); k++) {
						if ( cuts[i][k].first == j) {
						    l2g_insert_pts[call_inst].insert(arg_index);
#ifdef DEBUG
						    errs() << "\t\t\t\t\t(" << *val << ") crosses cut\n";
#endif
						}
					    }
					}
				    }
				}
			    }
			}
		    }
		}
	    }

#ifdef DEBUG
	    errs() << "}\n\n\n";
#endif


#ifdef DEBUG
	    errs() << "Inserting g2l functions...\n";
	    errs() << "{\n";
#endif
	    std::unordered_map<Function*, std::unordered_set<unsigned> > g2l_insert_pts;

	    // Decide g2l insert points
	    for (auto mi = l2g_insert_pts.begin(), me = l2g_insert_pts.end(); mi != me; mi++) {
		CallInst *call_inst = mi->first;
		Function *func = call_inst->getCalledFunction();
		// Skip library functions
		if (isLibraryFunction(func))
		    continue;

		for (auto si = mi->second.begin(), se = mi->second.end(); si != se; si++) {
		    unsigned arg_index = *si;
		    g2l_insert_pts[func].insert(arg_index);
		}
		
	    }


	    // Insert g2l functions
	    for (auto ii = g2l_insert_pts.begin(), ie = g2l_insert_pts.end(); ii != ie; ii++) {
		g2l_pointer_management_instrumentation(mod,  ii->first, ii->second);
	    }

#ifdef DEBUG
	    errs() << "}\n";
#endif

	    // Insert l2g functions
#ifdef DEBUG
	    errs() << "Inserting l2g functions...\n";
	    errs() << "{\n";
#endif
	    for (auto mi = l2g_insert_pts.begin(), me = l2g_insert_pts.end(); mi != me; mi++) {
		CallInst *call_inst = mi->first;
#ifdef DEBUG
		errs() << "\t" << (call_inst)->getParent()->getParent()->getName() << " " << mi->second.size() << "\n";
		errs() << "\t\t" << *call_inst << "\n";
#endif
		//  Insert l2g function before function calls wth address arguments
		for (auto si = mi->second.begin(), se = mi->second.end(); si != se; si++) {
		    unsigned arg_index = *si;
		    Value *operand = call_inst->getArgOperand(arg_index);
#ifdef DEBUG
		    //errs() << "\t\t\t" << *operand << "\n";
		    errs() << "\t\t\t" << arg_index << "\n";
#endif
		    IRBuilder<> builder(call_inst); // Instruction will be inserted before this instruction 
		    // Cast the value (in this case, a memory address) to be of char pointer type required by l2g function
		    Value *l2g_arg = builder.CreatePointerCast(operand, Type::getInt8PtrTy(context), "l2g_arg"); 
		    // Call the function l2g with the value with cast type
		    Value *l2g_ret = builder.CreateCall(func_l2g, l2g_arg, "l2g_ret"); 
		    // Cast the result back to be of the original type
		    Value *l2g_result = builder.CreatePointerCast(l2g_ret, operand->getType(), "l2g_result"); 
		    // Replace the use of the original memory address with the translated address
		    call_inst->setOperand(arg_index, l2g_result); 
		}
	    }
#ifdef DEBUG
	    errs() << "}\n\n\n";
#endif

	    // Step 3: insert stack management functions
	    // Insert stack management functions according to SSDM cuts
#ifdef DEBUG
	    errs() << "Inserting management functions according to SSDM cuts... {\n";
#endif

	    // Decide the insertion points of stack management function according to SSDM output
	    std::unordered_set <CallInst *> stack_management_insert_pts;
	    for (auto cuti = cuts.begin(), cute = cuts.end(); cuti != cute; cuti++) {
		for (size_t vi = 0; vi < cuti->second.size(); vi++) {
		    unsigned i, j;
		    std::string func_name;
		    i = cuti->first;
		    j = cuti->second[vi].first;
		    func_name = cuti->second[vi].second;
		    assert(paths[i][j]->first && paths[i][j]->second);
		    CallInst *call_inst = dyn_cast<CallInst> (paths[i][j]->first);
		    assert(call_inst);
		    stack_management_insert_pts.insert(call_inst);
		}
	    }
	    // Insert stack management functions 
	    for (auto si = stack_management_insert_pts.begin(), se = stack_management_insert_pts.end(); si != se; si++) {
		    CallInst *call_inst = *si;

		    // Insert stack management functions
		    stack_management_instrumentation(mod, call_inst);
	    }

#ifdef DEBUG
	    errs() << "}\n";
#endif

	    // Insert management functions at self-recursive calls
#ifdef DEBUG
	    errs() << "Inserting management functions around recursive calls... {\n";
#endif
	    for (std::unordered_set <CallGraphNode *>::iterator  si = undecidable_cgns.begin(), se = undecidable_cgns.end(); si != se; si++) {
		CallGraphNode * cgn = *si;
		// Skip external nodes
		if (!cgn->getFunction())
		    continue;
#ifdef DEBUG
		errs() << cgn->getFunction()->getName() << "\n";
#endif
		for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
		    // Skip non-self-recursive calls
		    if (cgni->second != cgn)
			continue;
		    CallInst *call_inst = dyn_cast<CallInst> (cgni->first);
		    assert(call_inst);

		    // Check if stack management functions have been inserted
		    BasicBlock::iterator ii(call_inst);
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
		    // Insert stack management functions
		    stack_management_instrumentation(mod, call_inst);
		}
	    }

#ifdef DEBUG
	    errs() << "}\n";
#endif

	    // Step 4: transform the main function to an user-defined function (this step will destroy call graph, so it must be in the last)
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

