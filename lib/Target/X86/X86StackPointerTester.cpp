//
//  RMDStackManager.cpp
//  TestBackEnd
//
//  Created by Bryce Holton on 6/23/14.
//  Copyright (c) 2014 Bryce Holton. All rights reserved.
//

#include "X86.h"
#include "X86TargetMachine.h"
#include "X86InstrInfo.h"
#include "MCTargetDesc/X86BaseInfo.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/PassManager.h"
#include "llvm/CodeGen/MachineConstantPool.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/DebugInfo.h"

#include <string.h>
#include <string>

using namespace llvm;

namespace llvm
{
    struct X86StackPointerTester : public MachineFunctionPass
    {
        
    public:
        TargetMachine &TM;
        static char ID;// Pass identification, replacement for typeid
        
        //**********************************************************************
        // constructor
        //**********************************************************************
        X86StackPointerTester(TargetMachine &tm) : MachineFunctionPass(ID), TM(tm) {}
        
        bool compareCallToFunctionNames(std::string function_name)
        {
            std::string function_names[] = {"test_func"};
            for (int i = 0; i < 5; i++)
            {
                if (function_names[i].compare(function_name) == 0)
                {
                    return true;
                }
            }
            return false;
        }
        bool runOnMachineFunction(MachineFunction &MF)
        {
            // Iterate over each basic block
            for(MachineFunction::iterator bItr = MF.begin(); bItr != MF.end(); ++bItr)
            {
                bool foundTestFunc = false;
                // Iterate over each instruction
                for(MachineBasicBlock::iterator iItr = bItr->begin(); iItr != bItr->end(); ++iItr)
                {
                    if (foundTestFunc)
                    {
                        errs() << *iItr << "\n";
                    }
                    // Find out if instruction is a function call.
                    if ( iItr->isCall() )
                    {
                        MachineOperand MO = iItr->getOperand(0); // Get first operand of machine instruction, contains function name.
                        const GlobalValue *GV = MO.getGlobal(); // The first operand is actually a global address.
                        std::string funcName = GV->getName(); // The global address of a function call has a function name property.
                        
                        // Find out if it is not a call to any of our libraries.
                        if ( !compareCallToFunctionNames(funcName) )
                        {
                            foundTestFunc = false;
                        }
                        else
                        {
                            foundTestFunc = true;
                        }
                    }
                }
            }
            return true;
        }
    };
    
    char X86StackPointerTester::ID = 0;
    FunctionPass *createStackPointerTester(X86TargetMachine &TM)
    {
        return new X86StackPointerTester(TM);
    }
}
