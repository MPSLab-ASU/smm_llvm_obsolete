#include "llvm/IR/Function.h"

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
