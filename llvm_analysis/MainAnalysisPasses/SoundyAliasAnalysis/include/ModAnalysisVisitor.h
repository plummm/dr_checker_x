//
// Created by hz on 4/5/19.
//

#ifndef PROJECT_MODANALYSISVISITOR_H
#define PROJECT_MODANALYSISVISITOR_H

#include "ModuleState.h"
#include "VisitorCallback.h"
#include "TaintInfo.h"
#include "TaintUtils.h"
#include "../../Utils/include/InstructionUtils.h"

using namespace llvm;

namespace DRCHECKER {

    //#define DEBUG_MOD_INSTR_VISIT

    /***
     * The main class that implements the modification analysis for global states.
     */
    class ModAnalysisVisitor : public VisitorCallback {

    public:
        GlobalState &currState;
        Function *targetFunction;
        AnalysisContext *actx;

        // context of the analysis, basically list of call sites
        std::vector<Instruction *> *currFuncCallSites;

        ModAnalysisVisitor(GlobalState &targetState,
                             Function *toAnalyze,
                             std::vector<Instruction *> *srcCallSites): currState(targetState) {
            this->targetFunction = toAnalyze;
            // Initialize the call site list
            this->currFuncCallSites = srcCallSites;
            // ensure that we have a context for current function.
            this->actx = targetState.getOrCreateContext(this->currFuncCallSites);
        }

        ~ModAnalysisVisitor() {
        }

        virtual void visit(Instruction &I) {
#ifdef DEBUG_MOD_INSTR_VISIT
            dbgs() << "Visiting instruction(In ModAnalysis): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        }

        virtual void visitStoreInst(StoreInst &I);

        virtual VisitorCallback* visitCallInst(CallInst &I, Function *targetFunction,
                                               std::vector<Instruction *> *oldFuncCallSites,
                                               std::vector<Instruction *> *currFuncCallSites);

        void analyzeModPattern(StoreInst &I, std::set<std::pair<long, Value*>> *targetObjects);

        virtual void visitBranchInst(BranchInst &I);

        virtual void visitICmpInst(ICmpInst &I);

        int verifyPatternExistence(Value* v, std::set<std::pair<long, Value*>> *targetObjects, int64_t *cn, int64_t *cn_o);

        int getArithmeticsInf(Value*,TRAIT*,int64_t,int64_t);

        //TODO: Are there instructions other than "store" that can update a variable? 

    }; //ModAnalysisVisitor class definition

} //namespace DRCHECKER

#endif //PROJECT_MODANALYSISVISITOR_H
