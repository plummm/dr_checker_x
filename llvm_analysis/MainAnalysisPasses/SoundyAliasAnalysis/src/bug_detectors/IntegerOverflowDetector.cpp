//
// Created by machiry on 1/31/17.
//

#include "bug_detectors/IntegerOverflowDetector.h"
#include "TaintUtils.h"

using namespace llvm;

namespace DRCHECKER {
//The instruction def for llvm 3.8
/*
 FIRST_BINARY_INST(11)
 HANDLE_BINARY_INST(11, Add  , BinaryOperator)
 HANDLE_BINARY_INST(12, FAdd , BinaryOperator)
 HANDLE_BINARY_INST(13, Sub  , BinaryOperator)
 HANDLE_BINARY_INST(14, FSub , BinaryOperator)
 HANDLE_BINARY_INST(15, Mul  , BinaryOperator)
 HANDLE_BINARY_INST(16, FMul , BinaryOperator)
 ......
*/
//#define BIN_OP_START 11
//#define BIN_OP_END 16

//The instruction def for llvm 9.0
//
/* FIRST_BINARY_INST(13)
HANDLE_BINARY_INST(13, Add  , BinaryOperator)
HANDLE_BINARY_INST(14, FAdd , BinaryOperator)
HANDLE_BINARY_INST(15, Sub  , BinaryOperator)
HANDLE_BINARY_INST(16, FSub , BinaryOperator)
HANDLE_BINARY_INST(17, Mul  , BinaryOperator)
HANDLE_BINARY_INST(18, FMul , BinaryOperator)
HANDLE_BINARY_INST(19, UDiv , BinaryOperator)
HANDLE_BINARY_INST(20, SDiv , BinaryOperator)
HANDLE_BINARY_INST(21, FDiv , BinaryOperator)
......
*/
#define BIN_OP_START 13
#define BIN_OP_END 18
//#define ONLY_ONE_WARNING
#define DEBUG_VISIT_BIN_OP

    void IntegerOverflowDetector::visitBinaryOperator(BinaryOperator &I) {
        unsigned long opCode = I.getOpcode();
        // warning already raised for this instruction in the current calling context. 
        if (this->warnedInstructions.find(&I) != this->warnedInstructions.end()) {
            return;
        }
        // if the binary operation is overflow inducing?
        if (opCode >= BIN_OP_START && opCode <= BIN_OP_END) {
            std::set<TaintFlag*> resultingTaintInfo;
            resultingTaintInfo.clear();
            std::set<Value*> targetValues;
            // add both the operands into values to be checked.
            targetValues.insert(I.getOperand(0));
            targetValues.insert(I.getOperand(1));
            for (auto currVal : targetValues) {
                std::set<TaintFlag*> *srcTaintInfo = TaintUtils::getTaintInfo(this->currState,
                                                                              this->currFuncCallSites,
                                                                              currVal);
                if (srcTaintInfo != nullptr) {
                    resultingTaintInfo.insert(srcTaintInfo->begin(), srcTaintInfo->end());
                }
            }
            if (resultingTaintInfo.empty()) {
                return;
            }
#ifdef DEBUG_VISIT_BIN_OP
            dbgs() << "IntegerOverflowDetector::visitBinaryOperator(): visit a bin op w/ TFs: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
            // raise warning for each of the tainted values.
            for (TaintFlag *currFlag : resultingTaintInfo) {
                //We want to detect high-order taint style vulnerabilities here, so we cannot only simply look at the current TaintFlag,
                //because it may originate from a non-user initiated dummy taint source (e.g. a global var), we must carefully inspect
                //and do a post-processing to see whether we can construct a taint chain (may survive multiple entry functions and 
                //invocations) that starts from a user input and ends at current instruction.
                if (!currFlag || !currFlag->isTainted()) {
                    continue;
                }
#ifdef DEBUG_VISIT_BIN_OP
                dbgs() << "IntegerOverflowDetector::visitBinaryOperator(): got a TF: ";
                currFlag->dumpInfo_light(dbgs());
#endif
                std::set<std::vector<InstLoc*>*> tchains;
                this->currState.getAllUserTaintChains(currFlag,tchains);
                if (tchains.empty()) {
                    //No taint from user inputs.
                    continue;
                }
#ifdef DEBUG_VISIT_BIN_OP
                dbgs() << "IntegerOverflowDetector::visitBinaryOperator(): we can construct a user taint chain for this TF, fire a warning!\n";
#endif
                std::string warningMsg = "Potential overflow, using tainted value in binary operation.";
                VulnerabilityWarning *currWarning = new VulnerabilityWarning(this->currFuncCallSites,
                                                                             &tchains,
                                                                             warningMsg, &I,
                                                                             TAG);
                this->currState.addVulnerabilityWarning(currWarning);
                if (this->warnedInstructions.find(&I) == this->warnedInstructions.end()) {
                    this->warnedInstructions.insert(&I);
                }
#ifdef ONLY_ONE_WARNING
                return;
#endif
            }
        }
    }

    VisitorCallback* IntegerOverflowDetector::visitCallInst(CallInst &I, Function *targetFunction,
                                                            std::vector<Instruction *> *oldFuncCallSites,
                                                            std::vector<Instruction *> *currFuncCallSites) {
        if (!targetFunction->isDeclaration()) {
            // only if the function has source.

            IntegerOverflowDetector *newVis = new IntegerOverflowDetector(this->currState, targetFunction,
                                                                  currFuncCallSites, this->targetChecker);

            return newVis;
        }
        return nullptr;
    }
}
