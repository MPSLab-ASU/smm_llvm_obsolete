#ifndef __MYFUNCTION_H__
#define __MYFUNCTION_H__

#include "llvm/IR/Function.h"

using namespace llvm;

bool isLibraryFunction(Function *);
bool isStackManagementHelperFunction(Function *);
bool isStackManagementFunction(Function *);

#endif
