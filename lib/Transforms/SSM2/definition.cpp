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

#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "definition.h"

using namespace llvm;

// Check if the use specified is an use of heap data
inline bool isHeapData(Value *val) {
    if (CallInst *call_inst = dyn_cast<CallInst>(val))
	if (call_inst->getCalledFunction()->getName() == "malloc")
	    return true;
    return false;
}

// Return all the definitions and the segment each resides of the Value specified by val
std::vector <std::pair<Value *, Segment> > getDefs(Value *val, std::unordered_map <Function *, std::vector<CallInst *> > &refs) {
    static std::unordered_set <Value *> def_stack;
    std::vector <std::pair<Value *, Segment> > res;
    def_stack.insert(val);

    if(def_stack.size() > 100)
	exit(-1);

    if (ConstantExpr *const_expr = dyn_cast<ConstantExpr>(val)) {
	//inst = const_expr->getAsInstruction();
	val = const_expr->getOperand(0);
    }

    if (dyn_cast<GlobalVariable>(val) || val->getName() == "argv") { 
	// The Value uses global data
	res.push_back(std::make_pair(val, DATA));
    } else if (isHeapData(val)) { 
	// The Value uses heap data
	res.push_back(std::make_pair(val, HEAP));
    } else if (Argument *arg = dyn_cast<Argument>(val)) { // The value is an argument
	// Get the function that contains the argument
	Function* callee = arg->getParent();
	// Go through all the references of the function and recursively find the definitions of the argument value of interest
	for (size_t i = 0; i < refs[callee].size(); i++) {
	    CallInst *call_inst = refs[callee][i];
	    Value *call_arg = call_inst->getArgOperand(arg->getArgNo());
	    // Skip back edges
	    if (def_stack.find(call_arg) == def_stack.end()) {
		std::vector <std::pair<Value *, Segment >> sub_res = getDefs(call_arg, refs);
		for (size_t j = 0; j < sub_res.size(); j++)
		    res.push_back(sub_res[j]);
	    }
	}
    } else { 

	// Check if the Value is a function pointer
	if( PointerType *ptr_ty = dyn_cast<PointerType>(val->getType())) {
	    if (ptr_ty->getElementType()->isFunctionTy()) {
		res.push_back(std::make_pair(val, HEAP));
		return res;
	    }
	}
	// Preprocess the value
	Instruction *inst = dyn_cast <Instruction> (val);
	assert(inst);

	std::vector <std::pair<Value *, Segment >> sub_res;
	switch (inst->getOpcode()) {
	    case Instruction::Alloca: 
		// The Value specified uses stack variable
		res.push_back(std::make_pair(val, STACK));
		break;
	    case Instruction::Call:
		//The rationale is function call should only return pointers to heap or global data
		res.push_back(std::make_pair(val, HEAP));
		break;
	    case Instruction::BitCast:
	    case Instruction::GetElementPtr:
	    case Instruction::Load:
		// Ignore back edges
		if (def_stack.find(inst->getOperand(0)) == def_stack.end()) {
		    sub_res = getDefs(inst->getOperand(0), refs);
		    for (size_t j = 0; j < sub_res.size(); j++)
			res.push_back(sub_res[j]);
		}
		break;
	    case Instruction::Select: 
		{
		    SelectInst* select_inst = dyn_cast<SelectInst> (inst);
		    Value* true_branch = select_inst->getTrueValue();
		    Value * false_branch = select_inst->getFalseValue(); 
		    // Skip back edges
		    if (def_stack.find(true_branch) == def_stack.end()) {
			sub_res = getDefs(true_branch, refs);
			for (size_t j = 0; j < sub_res.size(); j++)
			    res.push_back(sub_res[j]);
		    }
		    // Skip back edges
		    if (def_stack.find(false_branch) == def_stack.end()) {
			sub_res = getDefs(false_branch, refs);
			for (size_t j = 0; j < sub_res.size(); j++)
			    res.push_back(sub_res[j]);
		    }
		}
		break;
	    case Instruction::PHI: 
		{
		    PHINode *phi_inst = dyn_cast<PHINode>(inst);
		    for (unsigned i = 0; i < phi_inst->getNumIncomingValues(); i++) {
			// Skip back edges
			if (def_stack.find(phi_inst->getIncomingValue(i)) == def_stack.end()) {
			    sub_res = getDefs(phi_inst->getIncomingValue(i), refs);
			    for (size_t j = 0; j < sub_res.size(); j++)
				res.push_back(sub_res[j]);
			}
		    }
		}
		break;
	    default:
		res.push_back(std::make_pair(val, UNDEF));
	}
    }
    def_stack.erase(val);
    return res;
}
