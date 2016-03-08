#include "llvm/IR/Function.h"

using namespace llvm;

// Checks whether a function is a library function (including intrinsic functions)
bool isLibraryFunction(Function *func) {
    return (func->isDeclaration()); 
} 

// Check if a function is code management function	
bool isCodeManagementFunction(Function *func)
{
    if (func->getName().count("c_get") ==1)
	return true;
    if (func->getName().count("c_call") ==1)
	return true;
    if (func->getName().count("c_init") ==1)
	return true;
    if (func->getName().count("dma") ==1) 
	return true;
    return false;
}


