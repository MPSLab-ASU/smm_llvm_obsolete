#ifndef __INSTRUMENTATION_H__
#define __INSTRUMENTATION_H__

#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"

#include <unordered_set>


using namespace llvm;

void g2l_instrumentation(Module &, Function *, std::unordered_set<unsigned> &);
void stack_frame_management_instrumentation (Module &, CallInst *);

#endif
