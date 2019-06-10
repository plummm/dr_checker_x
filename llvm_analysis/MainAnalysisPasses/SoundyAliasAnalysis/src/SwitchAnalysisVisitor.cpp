//
// Created by hz on 4/25/19.
//

#include "SwitchAnalysisVisitor.h"
#include "InstructionUtils.h"

using namespace llvm;
namespace DRCHECKER {

    //#define DEBUG_CALL_INST
    #define DEBUG_VISIT_SWITCH_INST

    void SwitchAnalysisVisitor::visitSwitchInst(SwitchInst &I) {
#ifdef DEBUG_VISIT_SWITCH_INST
        dbgs() << "SwitchAnalysisVisitor::visitSwitchInst: \n";
        InstructionUtils::printInst(&I,dbgs());
#endif
        //Make sure that the switch variable is the "cmd" arg.
        Value *cond_var = I.getCondition();
        if ((!cond_var) || cond_var->getName().empty() || cond_var->getName().str() != "cmd") {
            return;
        }
        BasicBlock * def_bb = I.getDefaultDest();
        unsigned num = I.getNumCases();
#ifdef DEBUG_VISIT_SWITCH_INST
        dbgs() << "Cond Var: ";
        cond_var->print(dbgs());
        dbgs() << " Default BB: ";
        if(def_bb){
            dbgs() << def_bb->getName().str();
        }
        dbgs() << " #cases: " << num << "\n";
#endif
        for(auto c : I.cases()){
            ConstantInt *val = c.getCaseValue();
            //int64_t c_val = val->getSExtValue();
            uint64_t c_val = val->getZExtValue();
            BasicBlock *bb = c.getCaseSuccessor();
#ifdef DEBUG_VISIT_SWITCH_INST
            dbgs() << "Cond Val: " << c_val;
            dbgs() << " Dst BB: " << bb->getName().str() << "\n";
#endif
            this->currState.switchMap[bb].insert(c_val);
            //We also need to add this case successor's successors to the map, since they can also be reached from current case value.
            std::set<BasicBlock*> *succs = this->get_all_successors(bb);
            for(BasicBlock *succ_bb : *succs){
                this->currState.switchMap[succ_bb].insert(c_val);
            }
        }
    }

    std::set<BasicBlock*>* SwitchAnalysisVisitor::get_all_successors(BasicBlock *bb) {
        if(this->succ_map.find(bb) != this->succ_map.end()){
            return &this->succ_map[bb];
        }
        for(succ_iterator sit = succ_begin(bb), set = succ_end(bb); sit != set; ++sit) {
            BasicBlock *curr_bb = *sit;
            this->succ_map[bb].insert(curr_bb);
            if(this->succ_map.find(curr_bb) == this->succ_map.end()){
                this->get_all_successors(curr_bb);
            }
            this->succ_map[bb].insert(this->succ_map[curr_bb].begin(),this->succ_map[curr_bb].end());
        }
        return &this->succ_map[bb];
    }

    void SwitchAnalysisVisitor::visit(BasicBlock *BB) {
    }

    //There can be layered ioctl calls which all have the switch-case structure for the same user passed-in "cmd" argument,
    //so the SwitchAnalysisVisitor needs also process each callee.
    VisitorCallback* SwitchAnalysisVisitor::visitCallInst(CallInst &I, Function *currFunc,
                                                         std::vector<Instruction *> *oldFuncCallSites,
                                                         std::vector<Instruction *> *callSiteContext) {
#ifdef DEBUG_CALL_INST
       dbgs() << "---------\nSwitch analysis visits call instruction: ";
       I.print(dbgs());
       dbgs() << "\n";
#endif
        // if this is a kernel internal function.
        if(currFunc->isDeclaration()) {
            //this->handleKernelInternalFunction(I, currFunc);
            return nullptr;
        }
        // create a new ModAnalysisVisitor
        SwitchAnalysisVisitor *vis = new SwitchAnalysisVisitor(currState, currFunc, callSiteContext);

        return vis;
    }

}// namespace DRCHECKER
