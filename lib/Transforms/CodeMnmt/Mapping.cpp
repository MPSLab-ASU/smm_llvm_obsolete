//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "mapping"

#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/YAMLTraits.h"

#include <fstream>
#include <iostream>
#include <string>
#include <vector>


using namespace llvm;

namespace {
	struct Mapping : public ModulePass { // Initialize mapping information
		static char ID; // Pass identification, replacement for typeid
		Mapping() : ModulePass(ID) {}

		/*
		Function *build_main (Module &M) {
			Module *mod = &M;
			ConstantInt* const_int32_227 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10));
			Function* func__Z6c_mainiPPc = mod->getFunction("_Z6c_main");
			assert(func__Z6c_mainiPPc);
			Function* func__Z10c_init_regiz = mod->getFunction("_Z10c_init_regiz");
			assert(func__Z10c_init_regiz);
			Function* func__Z10c_init_mapiz = mod->getFunction("_Z10c_init_mapiz");
			assert(func__Z10c_init_mapiz);

			PointerType* PointerTy_1 = PointerType::get(IntegerType::get(mod->getContext(), 8), 0);
			PointerType* PointerTy_35 = PointerType::get(PointerTy_1, 0);
			std::vector<Type*>FuncTy_100_args;
			FuncTy_100_args.push_back(IntegerType::get(mod->getContext(), 32));
			FuncTy_100_args.push_back(PointerTy_35);
			FunctionType* FuncTy_100 = FunctionType::get(
					IntegerType::get(mod->getContext(), 32),
					FuncTy_100_args,
					false);

			Function* func_main = NULL;
			func_main = Function::Create(
					FuncTy_100, //Type
					GlobalValue::ExternalLinkage, // Linkage
					"main", mod); //Name

			func_main->setCallingConv(CallingConv::C);
			AttributeSet func_main_PAL;
			SmallVector<AttributeSet, 4> Attrs;
			AttributeSet PAS;
			AttrBuilder B;
			B.addAttribute(Attribute::UWTable);
			PAS = AttributeSet::get(mod->getContext(), ~0U, B);
			Attrs.push_back(PAS);
			func_main_PAL = AttributeSet::get(mod->getContext(), Attrs);
			func_main->setAttributes(func_main_PAL);

			Function::arg_iterator args = func_main->arg_begin();
			Value* int32_arg_738 = args++;
			int32_arg_738->setName("arg");
			Value* ptr_argv_739 = args++;
			ptr_argv_739->setName("argv");
			BasicBlock* label_entry_740 = BasicBlock::Create(mod->getContext(), "entry",func_main,0);
			 // Block entry (label_entry_740)
			AllocaInst* ptr_retval_741 = new AllocaInst(IntegerType::get(mod->getContext(), 32), "retval", label_entry_740); 
			ptr_retval_741->setAlignment(4);
			AllocaInst* ptr_arg_addr_742 = new AllocaInst(IntegerType::get(mod->getContext(), 32), "arg.addr", label_entry_740);
			ptr_arg_addr_742->setAlignment(4);
			AllocaInst* ptr_argv_addr_743 = new AllocaInst(PointerTy_35, "argv.addr", label_entry_740);
			ptr_argv_addr_743->setAlignment(8);

			StoreInst* void_745 = new StoreInst(const_int32_227, ptr_retval_741, false, label_entry_740);
			StoreInst* void_746 = new StoreInst(int32_arg_738, ptr_arg_addr_742, false, label_entry_740);
			StoreInst* void_747 = new StoreInst(ptr_argv_739, ptr_argv_addr_743, false, label_entry_740);


			// Initialize the region table
			ConstantInt* const_int32_230 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("1"), 10));
			ConstantInt* const_int64_252 = ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"), 10));
			std::vector<Value*> int32_call_748_params;
			int32_call_748_params.push_back(const_int32_230);
			int32_call_748_params.push_back(const_int64_252);
			CallInst* int32_call_748 = CallInst::Create(func__Z10c_init_regiz, int32_call_748_params, "call", label_entry_740);


			// TO DO: Initialize the mapping table 
			std::vector<Map> mapping_table;
			std::vector<Value*> int32_call2_params;
			for (std::vector<Map>::iterator mi = mapping_table.begin(), me = mapping_table.end(); mi != me; mi++) {
			}

			CallInst* int32_call2 = CallInst::Create(func__Z10c_init_mapiz, int32_call2_params, "call2", label_entry_740);


			LoadInst* int32_755 = new LoadInst(ptr_arg_addr_742, "", false, label_entry_740);
			int32_755->setAlignment(4);
			LoadInst* ptr_756 = new LoadInst(ptr_argv_addr_743, "", false, label_entry_740);
			ptr_756->setAlignment(8);

			std::vector<Value*> int32_call3_params;
			int32_call3_params.push_back(int32_755);
			int32_call3_params.push_back(ptr_756);
			CallInst* int32_call3 = CallInst::Create(func__Z6c_mainiPPc, int32_call3_params, "call3", label_entry_740);


			ReturnInst::Create(mod->getContext(), const_int32_227, label_entry_740);
			return func_main;
		}
		*/

		virtual bool runOnModule (Module &mod) {
			//LLVMContext &context = mod.getContext();
			for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
				if (fi->getName() == "main") {
					fi->setName("_Z6c_main");
					//get_func_size();
					//build_main(mod);
					break;
				}
			}

			return true;
		}
	};
}

char Mapping::ID = 1;
static RegisterPass<Mapping> mapingPass("mapping", "Initialize mapping information)");
