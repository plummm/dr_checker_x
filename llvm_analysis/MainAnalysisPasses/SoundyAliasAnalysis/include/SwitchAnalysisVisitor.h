//
// Created by hz on 4/25/19.
//

#ifndef PROJECT_SWITCHANALYSISVISITOR_H
#define PROJECT_SWITCHANALYSISVISITOR_H

#include "ModuleState.h"
#include "VisitorCallback.h"

using namespace llvm;

namespace DRCHECKER {

    //#define DEBUG_SWITCH_ANALYSIS_VISIT_INST

    /***
     * The main class that implements the switch analysis for ioctl().
     */
    class SwitchAnalysisVisitor : public VisitorCallback {

    public:
        GlobalState &currState;
        Function *targetFunction;

        // context of the analysis, basically list of call sites
        std::vector<Instruction *> *currFuncCallSites;

        //The mapping from one BB to all its successors (recursively).
        std::map<BasicBlock*,std::set<BasicBlock*>> succ_map;

        SwitchAnalysisVisitor(GlobalState &targetState,
                             Function *toAnalyze,
                             std::vector<Instruction *> *srcCallSites): currState(targetState) {
            this->targetFunction = toAnalyze;
            // Initialize the call site list
            this->currFuncCallSites = srcCallSites;
            // ensure that we have a context for current function.
            targetState.getOrCreateContext(this->currFuncCallSites);
        }

        ~SwitchAnalysisVisitor() {
        }

        virtual void visit(Instruction &I) {
#ifdef DEBUG_SWITCH_ANALYSIS_VISIT_INST
            dbgs() << "Visiting instruction(In SwitchAnalysis):";
            I.print(dbgs());
            dbgs() << "\n";
#endif
        }

        virtual void visitSwitchInst(SwitchInst &I);

        virtual void visit(BasicBlock *BB);

        virtual VisitorCallback* visitCallInst(CallInst &I, Function *targetFunction,
                                               std::vector<Instruction *> *oldFuncCallSites,
                                               std::vector<Instruction *> *currFuncCallSites);

        std::set<BasicBlock*>* get_all_successors(BasicBlock*);

        void resolveImplicitCMD(CallInst &I, Function *currFunc, std::vector<Instruction *> *callSiteContext);

    }; //SwitchAnalysisVisitor class definition

} //namespace DRCHECKER

#endif //PROJECT_SWITCHANALYSISVISITOR_H
