#ifndef __FUNCTYPE_H__
#define __FUNCTYPE_H__

#include "llvm/IR/Function.h"

using namespace llvm;

bool isLibraryFunction(Function *);
bool isCodeManagementFunction(Function *);

#endif
