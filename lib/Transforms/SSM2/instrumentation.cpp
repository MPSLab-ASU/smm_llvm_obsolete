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

#include <unordered_set>

#include "function.h"

#define DEBUG

using namespace llvm;

void g2l_pointer_management_instrumentation(Module &mod, Function *func, std::unordered_set<unsigned> &arg_indices) {
    LLVMContext &context = mod.getContext();
    Function *func_g2l = mod.getFunction("_g2l");

#ifdef DEBUG
    errs() << "\t" << func->getName() << " : " << arg_indices.size() << "\n";
#endif

    unsigned arg_index = 0;
    for (Function::arg_iterator ai = func->arg_begin(), ae = func->arg_end(); ai != ae; ai++, arg_index++) {
	if ( arg_indices.find(arg_index) == arg_indices.end() )
	    continue;
	assert(ai->getType()->isPointerTy());
	// Find user instructions of pointer arguments and replace the uses with the result of calling g2l on the arguments
	//if (ai->getType()->isPointerTy()) { 
	Value *val = &*ai;
#ifdef DEBUG
	errs() << "\t\t" << *val << " " << val->getNumUses() << "\n";
#endif
	// Call l2g right after the declaration of the stack variable
	IRBuilder<> builder(func->getEntryBlock().getFirstInsertionPt()); // Instruction will be inserted before ii
	// Cast the value (in this case, a memory address) to be of char pointer type required by l2g function
	Value *g2l_arg = builder.CreatePointerCast(val, Type::getInt8PtrTy(context), "g2l_arg");
	// Call the function l2g with the value with cast type
	Value *g2l_ret = builder.CreateCall(func_g2l, g2l_arg, "g2l_ret");
	// Cast the result back to be of the original type
	Value *g2l_result = builder.CreatePointerCast(g2l_ret, val->getType(), "g2l_result");
	// Find the uses of original value and call g2l on them
	for (Value::use_iterator ui = val->use_begin(), ue = val->use_end(); ui != ue; ) {
	    // Move iterator to next use before the current use is destroyed
	    Use *u = &*ui++;
	    User *user = u->getUser();
	    Instruction *user_inst = dyn_cast<Instruction>(user);
	    assert(user_inst);
	    // Skip uses introduced by insertion of l2g functions
	    if (u->getUser()->getName().count("l2g") == 1)
		continue;
	    // Skip uses introduced by insertion of g2l functions
	    if (u->getUser()->getName().count("g2l") == 1)
		continue;
	    // Skip uses in function call
	    if (user_inst->getOpcode() == Instruction::Call)
		continue;
#ifdef DEBUG
	    errs() << "\t\t\t" << *user_inst << "\n";
#endif
	    // Replace the uses of the pointer argument
	    u->set(g2l_result);
	}
	//}
    }
}

void stack_management_instrumentation (Module &mod, CallInst *call_inst) {
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

    // Global Variables
    GlobalVariable* gvar_spm_stack_base = mod.getGlobalVariable("_spm_stack_base");
    GlobalVariable* gvar_spm_depth = mod.getGlobalVariable("_stack_depth");
    GlobalVariable* gvar_stack = mod.getGlobalVariable("_stack");

    // Functions
    //Function *func_main = mod.getFunction("main");
    Function *func_sstore = mod.getFunction("_sstore");
    Function *func_sload = mod.getFunction("_sload");

    // Inline Assembly
    InlineAsm *func_putSP = InlineAsm::get(functy_inline_asm, "mov $0, %rsp;", "*m,~{rsp},~{dirflag},~{fpsr},~{flags}",true);


    BasicBlock::iterator ii(call_inst);
    Instruction *next_inst = &*(++ii);

#ifdef DEBUG
    errs() << "\t" << *call_inst <<  " " << call_inst->getNumUses() << "\n";
#endif

    // Before the function call
    // Insert a sstore function
    CallInst::Create(func_sstore, "", call_inst);
    // Insert putSP(_spm_stack_base)
    CallInst::Create(func_putSP, gvar_spm_stack_base, "", call_inst);
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

    // Skip if the function does not have return value
    Type * retty = call_inst->getType();
    if (retty->isVoidTy())
	return;
    // Skip if the return value is never used
    if (call_inst->getNumUses() == 0) 
	return;
    // Save return value in a global variable temporarily until sload is executed if it is used
    // Always create a new global variable in case of recursive functions
    GlobalVariable *gvar = new GlobalVariable(mod, //Module
	    retty, //Type
	    false, //isConstant
	    GlobalValue::ExternalLinkage, //linkage
	    0, // Initializer
	    "_gvar"); //Name
    // Initialize the temporary global variable
    gvar->setInitializer(Constant::getNullValue(retty));
    // Save return value to the global variable before sload is called
    StoreInst *st_ret = new StoreInst(call_inst, gvar);
    st_ret->insertAfter(call_inst);

    for (Value::use_iterator ui_ret = call_inst->use_begin(), ue_ret = call_inst->use_end(); ui_ret != ue_ret;) {
	// Move iterator to next use before the current use is destroyed
	Use *u = &*ui_ret++;
	Instruction *user_inst = dyn_cast<Instruction>(u->getUser()); 
	assert(user_inst);
#ifdef DEBUG
	errs() <<  "\t\t" << *user_inst << "\n";
#endif
	if (StoreInst *st_inst = dyn_cast <StoreInst> (user_inst)) {
	    if (st_inst->getPointerOperand()->getName().count("_gvar") == 1) {
#ifdef DEBUG
		errs() << "\t\t\t" << st_inst->getPointerOperand()->getName() << "\n";
#endif
		continue;
	    }
	}

	Instruction *insert_point = user_inst;

	if (PHINode *phi_inst = dyn_cast<PHINode>(user_inst))
	    insert_point = phi_inst->getIncomingBlock(u->getOperandNo())->getTerminator();

	// Read the global variable
	LoadInst *ret_val = new LoadInst(gvar, "", insert_point);
	// Find the uses of return value and replace them
	u->set(ret_val);
    }
}
