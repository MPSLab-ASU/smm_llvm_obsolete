#ifndef __GCCFG_H__
#define __GCCFG_H__


#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"

#include <vector>
#include <string>
#include <unordered_map>
#include <utility>

using namespace llvm;

class GCCFG;
class GCCFGFunction;
class GCCFGBasicBlock;
class GCCFGInstruction;
class RegionStatus;

enum AnalysisType {MustAnalysis, PersistenceAnalysis};
enum AnalysisResult {Uncategorized, AlwaysHit, FirstMiss};

std::ostream& operator<<(std::ostream& out, AnalysisResult& ar);

// Global Call Control Flow Graph
class GCCFG {
    public:
	// Constructor 
	GCCFG(Pass *p);
	// Build the GCCFG
	void build();
	// Add a function
	void addFunction(GCCFGFunction *gfunc);

	// Run once to collect the number of accesses of functions
	void runOnce();

	// Get the type of analysis being performed
	AnalysisType getAnalysisType();
	// Analyze the GCCFG and return the result of analyses
	void analyze();
	// Return the result of analyses
	std::unordered_map <CallInst *, std::pair<AnalysisResult, AnalysisResult> > getAnalysisResult();
	// Check if the fix-point iteration converges
	bool converge();
	// Save the current region status to the previous region status
	void resetForNextIteration();
	// Reset the region status
	void resetForNextAnalysis();
	// Categorize all the call instructions within this program
	void categorize();
	// Print the GCCFG
	void print();
	// Print the categories
	void printCategory();

	Pass *p;
	std::unordered_map <Instruction *, BasicBlock* > firstMissCalls;
	//std::unordered_map <BasicBlock *, std::unordered_set <Instruction *> > lpFirstMissCalls;
    protected:
	// Perform must anlysis;
	void analyzeAlwaysHit();
	// Perform persistence anlysis;
	void analyzeFirstMiss();
	// Calculate the result of analyses
	void calculateAnalysisResult();
    private:
	CallGraph *cg;
	AnalysisType analysisType;
	std::vector<GCCFGFunction *> gFuncs;
	std::unordered_map <CallInst *, std::pair<AnalysisResult, AnalysisResult> > analysisResult;
};

// GCCFG function
class GCCFGFunction {
    public:
	// Constructor
	GCCFGFunction(GCCFG* gccfg, Function *func, unsigned long regionID);
	// Return the GCCFG this function belongs to
	GCCFG *getParent();
	// Return the name of this function
	std::string getName();
	// Return the entry basic block
	GCCFGBasicBlock *getEntryBlock();
	// Set the entry basic block
	void setEntryBlock(GCCFGBasicBlock *gEntryBlock);
	// Return the list of exit blocks in this function
	std::vector <GCCFGBasicBlock *> getExitBlocks();
	// Add the specified basic block to the list exit blocks
	void addExitBlock(GCCFGBasicBlock *gBB);
	// Return the list of basic blocks in this function
	std::vector <GCCFGBasicBlock *> getBasicBlocks();
	// Add the specified basic block
	void addBasicBlock(GCCFGBasicBlock *gBB);

	// Return the region ID this function is mapped to
	unsigned long getRegionID();

	// Run once to collect the number of accesses of functions
	void runOnce();
	// Initialize the states for analysis
	void initialize();
	// Return the number this function is accessed
	long getNumberAccessed();
	// Return the access number of this function
	long getAccessNumber();
	// Reset the access number this function 
	void resetAccessNumber();

	// Get the type of analysis being performed
	AnalysisType getAnalysisType();
	// Get the input region status of this function
	RegionStatus getInput();
	// Get the ouputput region status of this function
	RegionStatus getOutput();
	// Simulate the execution of the loops in this function
	void simulateLoops();
	// Simulate the specified loop 
	void simulate(BasicBlock *lpHeader);
	// Simulate the execution without considering back edges
	RegionStatus simulateThrough(RegionStatus &rs);
	// Simulate the execution 
	RegionStatus simulate(RegionStatus &rs);

	// Reset the region status
	void resetForNextAnalysis();
	// Categorize all the call instructions within the loop with the specified header
	void categorize(BasicBlock *lpHeader);
	// Print the categories
	void printCategory();
    private:
	// ID of the region this function maps to
	unsigned long regionID;
	// Current access number of this function
	long accessNum;
	// The number of times this function is accessed
	long numAccessed;
	GCCFG *gccfg;
	Function *func;
	std::string name;
	GCCFGBasicBlock *entryBB;
	std::vector<GCCFGBasicBlock *> returnBBs;
	std::vector<GCCFGBasicBlock *> gBBs;

	std::vector<RegionStatus *> inputs;
	std::vector<RegionStatus *> outputs;


	RegionStatus * throughInput;
	RegionStatus * throughOutput;
};

// GCCFG basic block
class GCCFGBasicBlock {
    public:
	GCCFGBasicBlock(BasicBlock *bb);
	// Return the corresponding LLVM basic block 
	BasicBlock *getLLVMBasicBlock();
	// Return the name of this basic block
	std::string getName();
	// Return number of predecessing basic blocks
	unsigned long getNumPredecessors();
	// Return the specified predecessor
	GCCFGBasicBlock *getPredecessor(unsigned long idx);
	// Add the specified basic block as a predecessor
	void addPredecessor(GCCFGBasicBlock *gbb);
	// Return number of succeeding GCCFG basic blocks
	unsigned long getNumSuccessors();
	// Return the specified successor
	GCCFGBasicBlock *getSuccessor(unsigned long idx);
	// Add the specified basic block as a successor
	void addSuccessor(GCCFGBasicBlock *gbb);
	// Return the GCCFG instructions
	std::vector <GCCFGInstruction *> getInstructions();
	// Add an instruction
	void addInstruction(GCCFGInstruction *gInst);


	// Run once to collect the number of accesses of functions
	void runOnce();
	// Initialize the states for analysis
	void initialize();
	// Return the access number of the parent function
	long getFunctionAccessNumber();
	// Get the type of analysis being performed
	AnalysisType getAnalysisType();
	// Get the ouputput region status of this basicblock
	RegionStatus getOutput();
	// Simulate the execution 
	RegionStatus simulate(RegionStatus &rs);
	// Simulate the execution without considering back edges
	RegionStatus simulateThrough(RegionStatus &rs);
	// Reset the region status
	void resetForNextAnalysis();
	// Print the categories
	void printCategory();

    private:
	BasicBlock *bb;
	std::string name;
	std::vector<GCCFGBasicBlock *> preds;
	std::vector<GCCFGBasicBlock *> succs;
	std::vector <GCCFGInstruction *> gInsts;

	std::vector<RegionStatus *> inputs;
	std::vector<RegionStatus *> outputs;
};

class GCCFGInstruction {
    public:
	GCCFGInstruction(Instruction *inst);
	// Return the instruction
	Instruction *getLLVMInstruction();


	// Run once to collect the number of accesses of functions
	void runOnce();
	// Initialize the states for analysis
	void initialize();
	// Return the access number of the parent function
	long getFunctionAccessNumber();
	// Get the input region status of this instruction
	RegionStatus getInput();
	// Get the output region status of this instruction
	RegionStatus getOutput();
	// Get the type of analysis being performed
	AnalysisType getAnalysisType();
	// Simulate the execution 
	RegionStatus simulate(RegionStatus &rs);
	// Simulate the execution without considering back edges
	RegionStatus simulateThrough(RegionStatus &rs);
	// Save the current region status to the previous region status
	void resetForNextIteration();
	// Reset the region status
	void resetForNextAnalysis();
	// Check if the input and out region status are the same with the previous run
	bool converge();
	// Categorize this call instruction for must analysis
	void categorize();
	// Categorize this call instruction within the loop with the specified header for persistence analysis
	void categorize(BasicBlock *lpHeader);
	// Print the categories
	void printCategory();

	// If the called function is already in the SPM before the execution of this (call) instruction
	std::vector<AnalysisResult> calleeAnalysis;
	AnalysisResult finalCalleeAnalysis;
	// If the caller function is in the SPM after the the execution of this (call) instruction
	std::vector<AnalysisResult> callerAnalysis;
	AnalysisResult finalCallerAnalysis;
    private:
	// The LLVM Instruction this instruction corresponds to
	Instruction *inst;

    public: // TODO debug only
	// The region status before fetching the called function
	std::vector<RegionStatus *> inputs;
	// The region status after fetching the called function
	std::vector<RegionStatus *> intermediates;
	// The region status after fetching the caller function
	std::vector<RegionStatus *> outputs;
	// The input region status in the previous run
	std::vector<RegionStatus *> previousInputs;
	// The output region status in the previous run
	std::vector<RegionStatus *> previousOutputs;
};

class RegionStatus {
    public:
	RegionStatus(unsigned long numRegions);
	bool empty();
	std::unordered_set <Function *> & operator[] (unsigned long regionID);
	bool operator==  (RegionStatus rhs);
	bool operator!=  (RegionStatus rhs);
	RegionStatus & operator= (RegionStatus rhs);
	RegionStatus operator&& (RegionStatus rhs);
	RegionStatus operator|| (RegionStatus rhs);
	void reset();
    private:
	std::vector< std::unordered_set <Function *> > regStat;
};


#endif
