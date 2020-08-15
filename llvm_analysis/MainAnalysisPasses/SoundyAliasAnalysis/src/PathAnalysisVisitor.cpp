//
// Created by hz on 8/13/20.
//

#include "PathAnalysisVisitor.h"

using namespace llvm;

namespace DRCHECKER {

    #define DEBUG_VISIT_SWITCH_INST
    //#define DEBUG_CALL_INST

    void PathAnalysisVisitor::visitSwitchInst(SwitchInst &I) {
#ifdef DEBUG_VISIT_SWITCH_INST
        dbgs() << "PathAnalysisVisitor::visitSwitchInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value *cond_var = I.getCondition();
        BasicBlock *def_bb = I.getDefaultDest();
        unsigned num = I.getNumCases();
#ifdef DEBUG_VISIT_SWITCH_INST
        dbgs() << "PathAnalysisVisitor::visitSwitchInst(): Cond Var: " << InstructionUtils::getValueStr(cond_var) << " Default BB: "
        << InstructionUtils::getBBStrID(def_bb) << " #cases: " << num << "\n";
#endif
        //Collect the cases and values of this switch.
        //case bb -> the switch value(s) to it.
        std::map<BasicBlock*,std::set<int64_t>> caseMap;
        for (auto c : I.cases()) {
            ConstantInt *val = c.getCaseValue();
            int64_t c_val = val->getSExtValue();
            //uint64_t c_val = val->getZExtValue();
            BasicBlock *bb = c.getCaseSuccessor();
#ifdef DEBUG_VISIT_SWITCH_INST
            dbgs() << "Case Value: " << c_val << " Dst BB: " << InstructionUtils::getBBStrID(bb) << "\n";
#endif
            if (!val || !bb) {
                continue;
            }
            //We now need to ensure that "bb" is dominated by the switch BB, otherwise we cannot enforce the constraints
            //posed by the switch inst to it.
            if (bb->getSinglePredecessor() != I.getParent()) {
                dbgs() << "!!! PathAnalysisVisitor::visitSwitchInst(): current case BB is not dominated by the switch BB!\n";
                continue;
            }
            caseMap[bb].insert(c_val);
        }
        //Now inspect each branch of this switch, test the feasibility, and update the constraints of "cond_var" in each branch.
        //First need to see whether there are existing constaints for the "cond_var" at this point.
        Constraint *c = this->currState.getConstraints(this->currFuncCallSites, cond_var, true);
        assert(c);
        for (auto &e : caseMap) {
            BasicBlock *bb = e.first;
            //Get all BBs dominated by "bb", these are BBs belonging only to the current case branch.
            std::set<BasicBlock*> dombbs;
            BBTraversalHelper::getDominatees(bb, dombbs);
        }
        //Get all BBs belonging to current case (i.e. BBs dominated by the heading case "bb").
        //TODO: default dest BBs
        return;
    }

    //There can be layered ioctl calls which all have the switch-case structure for the same user passed-in "cmd" argument,
    //so the SwitchAnalysisVisitor needs also process each callee.
    VisitorCallback* PathAnalysisVisitor::visitCallInst(CallInst &I, Function *currFunc,
                                                        std::vector<Instruction*> *oldFuncCallSites,
                                                        std::vector<Instruction*> *callSiteContext) {
        // if this is a kernel internal function.
        if(currFunc->isDeclaration()) {
            //this->handleKernelInternalFunction(I, currFunc);
            return nullptr;
        }
        // create a new ModAnalysisVisitor
        PathAnalysisVisitor *vis = new PathAnalysisVisitor(currState, currFunc, callSiteContext);
        return vis;
    }

    void PathAnalysisVisitor::visitBranchInst(BranchInst &I) {
        //
    }

}// namespace DRCHECKER
