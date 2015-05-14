#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"

using namespace llvm;

// Checks whether a function is a library function (including intrinsic functions)
bool isLibraryFunction(Function *func) {
    return (func->isDeclaration()); 
} 

// Check if a function is stack management helper function      
bool isStackManagementHelperFunction(Function *func) {
    if (func->getName().count("_get_func_stack_size") == 1)
	return true;
    if (func->getName().count("_dump_func_stack_sizes") == 1)
	return true;
    return false;
}


// Check if a function is stack management function	
bool isStackManagementFunction(Function *func) {
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


// Check if a global variable is used by stack mangagement    
bool isStackManagementVariable(GlobalVariable *gvar) {
    if (gvar->getName() == "_spm_begin")
	return true;
    if (gvar->getName() == "_spm_end")
	return true;
    if (gvar->getName() == "_spm_stack_base")
	return true;
    if (gvar->getName() == "_mem_stack_base")
	return true;
    if (gvar->getName() == "_stack_depth")
	return true;
    if (gvar->getName() == "_stack")
	return true;
    if (gvar->getName() == "sp")
	return true;
    if (gvar->getName() == "gaddr")
	return true;
    if (gvar->getName() == "laddr")
	return true;
    return false;
}

