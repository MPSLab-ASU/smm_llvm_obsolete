#ifndef __INSTRUMENTATION_H__
#define __INSTRUMENTATION_H__

#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"

using namespace llvm;

void l2g_pointer_management_instrumentation(Module &, CallGraphNode *);
void g2l_pointer_management_instrumentation(Module &, CallGraphNode *);
void stack_frame_management_instrumentation (Module &, CallInst *);

#endif
