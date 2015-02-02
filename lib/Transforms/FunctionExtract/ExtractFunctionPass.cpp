//===- ExtractFunction.cpp - Extract a function from Program --------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements several methods that are used to extract functions,
// loops, or portions of a module from the rest of the module.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FileUtilities.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"
#include <set>
using namespace llvm;

#define DEBUG_TYPE "bugpoint"
Module *
SplitFunctionsOutOfModule(Module *M,
                          const std::vector<Function*> &F,
                          ValueToValueMapTy &VMap);

namespace
{
    Function* globalInitUsesExternalBA(GlobalVariable* GV) {
        if (!GV->hasInitializer())
            return nullptr;
        
        Constant *I = GV->getInitializer();
        
        // walk the values used by the initializer
        // (and recurse into things like ConstantExpr)
        std::vector<Constant*> Todo;
        std::set<Constant*> Done;
        Todo.push_back(I);
        
        while (!Todo.empty()) {
            Constant* V = Todo.back();
            Todo.pop_back();
            Done.insert(V);
            
            if (BlockAddress *BA = dyn_cast<BlockAddress>(V)) {
                Function *F = BA->getFunction();
                if (F->isDeclaration())
                    return F;
            }
            
            for (User::op_iterator i = V->op_begin(), e = V->op_end(); i != e; ++i) {
                Constant *C = dyn_cast<Constant>(*i);
                if (C && !isa<GlobalValue>(C) && !Done.count(C))
                    Todo.push_back(C);
            }
        }
        return nullptr;
    }
    
    struct ExtractFunction : public ModulePass
    {
        static char ID; // Pass identification, replacement for typeid
        
        // Pass constructor
        ExtractFunction() : ModulePass(ID)
        {}
        
        // Pass destructor
        ~ExtractFunction()
        {}
        
        virtual bool runOnModule (Module &M)
        {
            ValueToValueMapTy NewVMap;
            CloneModule(&M, NewVMap);
            std::vector<Function*> vec;
            
            for (Module::iterator functionItr = M.begin(); functionItr != M.end(); ++functionItr)
            {
                errs() << functionItr->getName() << "\n";
                if (functionItr->getName().compare("print_path") == 0)
                {
                    vec.push_back(functionItr);
                    Module* newMod = SplitFunctionsOutOfModule(&M, vec, NewVMap);
                    errs() << *newMod;
                }
            }
            
            return false;
        }
    };
}  // end anonymous namespace

// DeleteFunctionBody - "Remove" the function by deleting all of its basic
// blocks, making it external.
//
void DeleteFunctionBody(Function *F) {
    // delete the body of the function...
    F->deleteBody();
    assert(F->isDeclaration() && "This didn't make the function external!");
}

/// GetTorInit - Given a list of entries for static ctors/dtors, return them
/// as a constant array.
static Constant *GetTorInit(std::vector<std::pair<Function*, int> > &TorList) {
    assert(!TorList.empty() && "Don't create empty tor list!");
    std::vector<Constant*> ArrayElts;
    Type *Int32Ty = Type::getInt32Ty(TorList[0].first->getContext());
    
    StructType *STy =
    StructType::get(Int32Ty, TorList[0].first->getType(), NULL);
    for (unsigned i = 0, e = TorList.size(); i != e; ++i) {
        Constant *Elts[] = {
            ConstantInt::get(Int32Ty, TorList[i].second),
            TorList[i].first
        };
        ArrayElts.push_back(ConstantStruct::get(STy, Elts));
    }
    return ConstantArray::get(ArrayType::get(ArrayElts[0]->getType(),
                                             ArrayElts.size()),
                              ArrayElts);
}

/// SplitStaticCtorDtor - A module was recently split into two parts, M1/M2, and
/// M1 has all of the global variables.  If M2 contains any functions that are
/// static ctors/dtors, we need to add an llvm.global_[cd]tors global to M2, and
/// prune appropriate entries out of M1s list.
static void SplitStaticCtorDtor(const char *GlobalName, Module *M1, Module *M2,
                                ValueToValueMapTy &VMap) {
    GlobalVariable *GV = M1->getNamedGlobal(GlobalName);
    if (!GV || GV->isDeclaration() || GV->hasLocalLinkage() ||
        !GV->use_empty()) return;
    
    std::vector<std::pair<Function*, int> > M1Tors, M2Tors;
    ConstantArray *InitList = dyn_cast<ConstantArray>(GV->getInitializer());
    if (!InitList) return;
    
    for (unsigned i = 0, e = InitList->getNumOperands(); i != e; ++i) {
        if (ConstantStruct *CS = dyn_cast<ConstantStruct>(InitList->getOperand(i))){
            if (CS->getNumOperands() != 2) return;  // Not array of 2-element structs.
            
            if (CS->getOperand(1)->isNullValue())
                break;  // Found a null terminator, stop here.
            
            ConstantInt *CI = dyn_cast<ConstantInt>(CS->getOperand(0));
            int Priority = CI ? CI->getSExtValue() : 0;
            
            Constant *FP = CS->getOperand(1);
            if (ConstantExpr *CE = dyn_cast<ConstantExpr>(FP))
                if (CE->isCast())
                    FP = CE->getOperand(0);
            if (Function *F = dyn_cast<Function>(FP)) {
                if (!F->isDeclaration())
                    M1Tors.push_back(std::make_pair(F, Priority));
                else {
                    // Map to M2's version of the function.
                    F = cast<Function>(VMap[F]);
                    M2Tors.push_back(std::make_pair(F, Priority));
                }
            }
        }
    }
    
    GV->eraseFromParent();
    if (!M1Tors.empty()) {
        Constant *M1Init = GetTorInit(M1Tors);
        new GlobalVariable(*M1, M1Init->getType(), false,
                           GlobalValue::AppendingLinkage,
                           M1Init, GlobalName);
    }
    
    GV = M2->getNamedGlobal(GlobalName);
    assert(GV && "Not a clone of M1?");
    assert(GV->use_empty() && "llvm.ctors shouldn't have uses!");
    
    GV->eraseFromParent();
    if (!M2Tors.empty()) {
        Constant *M2Init = GetTorInit(M2Tors);
        new GlobalVariable(*M2, M2Init->getType(), false,
                           GlobalValue::AppendingLinkage,
                           M2Init, GlobalName);
    }
}


/// SplitFunctionsOutOfModule - Given a module and a list of functions in the
/// module, split the functions OUT of the specified module, and place them in
/// the new module.
Module *SplitFunctionsOutOfModule(Module *M,
                                const std::vector<Function*> &F,
                                ValueToValueMapTy &VMap) {
    // Make sure functions & globals are all external so that linkage
    // between the two modules will work.
    for (Module::iterator I = M->begin(), E = M->end(); I != E; ++I)
        I->setLinkage(GlobalValue::ExternalLinkage);
    for (Module::global_iterator I = M->global_begin(), E = M->global_end();
         I != E; ++I) {
        if (I->hasName() && I->getName()[0] == '\01')
            I->setName(I->getName().substr(1));
        I->setLinkage(GlobalValue::ExternalLinkage);
    }
    
    ValueToValueMapTy NewVMap;
    Module *New = CloneModule(M, NewVMap);
    
    // Remove the Test functions from the Safe module
    std::set<Function *> TestFunctions;
    for (unsigned i = 0, e = F.size(); i != e; ++i)
    {
        Function *TNOF = cast<Function>(VMap[F[i]]);
        DEBUG(errs() << "Removing function ");
        DEBUG(TNOF->printAsOperand(errs(), false));
        DEBUG(errs() << "\n");
        errs() << "\n";
//        errs() << *NewVMap[TNOF] << "\n";
//        TestFunctions.insert(cast<Function>(NewVMap[TNOF]));
//        errs() << "here\n";
        DeleteFunctionBody(TNOF);       // Function is now external in this module!
    }
    
    
    // Remove the Safe functions from the Test module
    for (Module::iterator I = New->begin(), E = New->end(); I != E; ++I)
        if (!TestFunctions.count(I))
            DeleteFunctionBody(I);
    
   
    // Try to split the global initializers evenly
    for (Module::global_iterator I = M->global_begin(), E = M->global_end();
         I != E; ++I) {
        GlobalVariable *GV = cast<GlobalVariable>(NewVMap[I]);
        if (Function *TestFn = globalInitUsesExternalBA(I)) {
            if (Function *SafeFn = globalInitUsesExternalBA(GV)) {
                errs() << "*** Error: when reducing functions, encountered "
                "the global '";
                GV->printAsOperand(errs(), false);
                errs() << "' with an initializer that references blockaddresses "
                "from safe function '" << SafeFn->getName()
                << "' and from test function '" << TestFn->getName() << "'.\n";
                exit(1);
            }
            I->setInitializer(nullptr);  // Delete the initializer to make it external
        } else {
            // If we keep it in the safe module, then delete it in the test module
            GV->setInitializer(nullptr);
        }
    }
    
    // Make sure that there is a global ctor/dtor array in both halves of the
    // module if they both have static ctor/dtor functions.
    SplitStaticCtorDtor("llvm.global_ctors", M, New, NewVMap);
    SplitStaticCtorDtor("llvm.global_dtors", M, New, NewVMap);
    
    return New;
}

char ExtractFunction::ID = 0;
static RegisterPass<ExtractFunction>
X("extract-func", "Extract functions from a module and insert them into their own modules.");
