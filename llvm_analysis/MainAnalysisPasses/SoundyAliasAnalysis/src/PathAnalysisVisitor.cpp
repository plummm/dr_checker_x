//
// Created by hz on 8/13/20.
//

#include "PathAnalysisVisitor.h"

using namespace llvm;

namespace DRCHECKER {

    #define DEBUG_VISIT_SWITCH_INST
    #define DEBUG_CALL_INST

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
        std::set<int64_t> cns;
        for (auto c : I.cases()) {
            ConstantInt *val = c.getCaseValue();
            int64_t c_val = val->getSExtValue();
            //uint64_t c_val = val->getZExtValue();
            cns.insert(c_val);
            BasicBlock *bb = c.getCaseSuccessor();
#ifdef DEBUG_VISIT_SWITCH_INST
            dbgs() << "Case Value: " << c_val << " Dst BB: " << InstructionUtils::getBBStrID(bb) << "\n";
#endif
            if (!val || !bb) {
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
            //We now need to ensure that "bb" is dominated by the switch BB, otherwise we cannot enforce the constraints
            //posed by the switch inst to it.
            if (InstructionUtils::getSinglePredecessor(bb) != I.getParent()) {
                dbgs() << "!!! PathAnalysisVisitor::visitSwitchInst(): current case BB is not dominated by the switch BB!\n";
                continue;
            }
            //Get all BBs dominated by "bb", these are BBs belonging only to the current case branch.
            std::set<BasicBlock*> dombbs;
            BBTraversalHelper::getDominatees(bb, dombbs);
            //Update the constraints.
            expr cons = c->getEqvExpr(e.second);
            c->addConstraint2BBs(&cons,dombbs);
        }
        //Deal with the default case.
        if (def_bb && InstructionUtils::getSinglePredecessor(def_bb) == I.getParent()) {
            std::set<BasicBlock*> dombbs;
            BBTraversalHelper::getDominatees(def_bb, dombbs);
            expr e = c->getNeqvExpr(cns);
            c->addConstraint2BBs(&e,dombbs);
        }
        //Now let's see whether there are any infeasible BBs due to the constraint conflicts, if any, update them to
        //the global state in order to guide the BB exploration.
        this->currState.updateDeadBBs(this->currFuncCallSites, c->deadBBs);
        return;
    }

    VisitorCallback* PathAnalysisVisitor::visitCallInst(CallInst &I, Function *currFunc,
                                                        std::vector<Instruction*> *oldFuncCallSites,
                                                        std::vector<Instruction*> *callSiteContext) {
#ifdef DEBUG_CALL_INST
        dbgs() << "PathAnalysisVisitor::visitCallInst(): " << InstructionUtils::getValueStr(&I) << ", callee: " 
        << currFunc->getName().str() << "\n";
#endif
        // if this is a kernel internal function, just skip it for now.
        if(currFunc->isDeclaration()) {
            //this->handleKernelInternalFunction(I, currFunc);
            return nullptr;
        }
        // Ok, we need to propagate the constraints from the actual args to the formal args, if any.
        int arg_no = -1;
        for (Value *arg : I.args()) {
            ++arg_no;
            //Get the formal argument.
            Argument *farg = InstructionUtils::getArg(currFunc,arg_no);
            if (!arg || !farg) {
                continue;
            }
            Constraint *nc = nullptr;
            if (!dyn_cast<ConstantInt>(arg)) {
                //The actual argument is a variable, see whether it has any constraints at current point.
                Constraint *cons = this->currState.getConstraints(this->currFuncCallSites, arg, false);
                if (!cons) {
                    //Try to strip the pointer cast.
                    cons = this->currState.getConstraints(this->currFuncCallSites, arg->stripPointerCasts(), false);
                }
                if (!cons) {
                    // No constraints for current actual arg.
                    continue;
                }
                expr *e = cons->getConstraint(I.getParent());
                if (!e) {
                    // No constraints in current BB.
                    continue;
                }
#ifdef DEBUG_CALL_INST
                dbgs() << "PathAnalysisVisitor::visitCallInst(): propagate constraint for arg " << arg_no
                << ": " << InstructionUtils::getValueStr(arg) << " -> " << InstructionUtils::getValueStr(farg) 
                << ", constraint: " << e->to_string() << "\n";
#endif
                nc = new Constraint(cons,farg,currFunc);
                nc->addConstraint2AllBBs(e);
            }else {
                //The actual argument is a constant, so obviously we need to add a constraint to the formal arg.
                nc = new Constraint(farg,currFunc);
                int64_t c_val = dyn_cast<ConstantInt>(arg)->getSExtValue();
                std::set<int64_t> vs;
                vs.insert(c_val);
                expr e = nc->getEqvExpr(vs);
#ifdef DEBUG_CALL_INST
                dbgs() << "PathAnalysisVisitor::visitCallInst(): actual arg " << arg_no << " is a constant int: "
                << c_val << ", so add the constraint " << e.to_string() << " to the formal arg: " 
                << InstructionUtils::getValueStr(farg) << "\n";
#endif
                nc->addConstraint2AllBBs(&e);
            }
            //Add the formal arg constraint to the global state.
            this->currState.setConstraints(callSiteContext,farg,nc);
        }
        // In the end create a new PathAnalysisVisitor for the callee.
        PathAnalysisVisitor *vis = new PathAnalysisVisitor(currState, currFunc, callSiteContext);
        return vis;
    }

    //TODO
    void PathAnalysisVisitor::visitBranchInst(BranchInst &I) {
        //
    }

}// namespace DRCHECKER
