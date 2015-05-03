#ifndef __PREDICATE_H__
#define __PREDICATE_H__

#include "llvm/IR/Function.h"

using namespace llvm;

bool isLibraryFunction(Function *);
bool isStackManagementHelperFunction(Function *);
bool isStackManagementFunction(Function *);

#endif
