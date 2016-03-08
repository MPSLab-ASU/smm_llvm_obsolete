#ifndef __DATAFLOW_H__
#define __DATAFLOW_H__

#include "llvm/IR/Instruction.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Value.h"

#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using namespace llvm;

enum Segment { DATA, HEAP, STACK, UNDEF };

inline bool isHeapData(Value *val);

std::vector <std::pair<Value *, Segment> > getDefs(Value *, std::unordered_map <Function *, std::vector<CallInst *> > &);

#endif
