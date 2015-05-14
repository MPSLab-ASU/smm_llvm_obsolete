#ifndef __INSTRUMENTATION__H__
#define __INSTRUMENTATION__H__

#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Module.h"


using namespace llvm;

void stack_pointer_management_instrumentation(Module &, CallGraphNode *);
void l2g_pointer_management_instrumentation(Module &, CallGraphNode *);
void g2l_pointer_management_instrumentation(Module &, CallGraphNode *);

#endif
