//
// Created by hz on 4/25/19.
//

#include "SwitchAnalysisVisitor.h"
#include "InstructionUtils.h"

using namespace llvm;
namespace DRCHECKER {

    //#define DEBUG_CALL_INST
    #define DEBUG_VISIT_SWITCH_INST
    #define RESOLVE_IMPLICIT_CMD
    #define DEBUG_RESOLVE_IMPLICIT_CMD

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
        BasicBlock *cur_bb = I.getParent();
        std::set<uint64_t> leadCmd;
        if (cur_bb && this->currState.switchMap.find(cur_bb) != this->currState.switchMap.end()) {
            //This means there are some cmd values that can lead to this BB where we encounter a new cmd switch, 
            //this can happen if there are multiple cmd switches in a same function, e.g.
            //switch(cmd){case 0: ...; case 1: ...;} ... switch(cmd){case 2: .X.; case 3: .Y.;}
            //If we want to reach X, the previous analysis may tell us case 0 and 1 will lead to X since it's the successor
            //of the previous "switch", while in fact we should exclude case 0 and 1 (i.e. block the leading cmds here) and only reserve case 2.
            leadCmd = this->currState.switchMap[cur_bb];
        }
        BasicBlock *def_bb = I.getDefaultDest();
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
        //Since we are encountering a new cmd switch, we need to "block" all previous cmds that can reach here,
        //which can happen if there are multiple cmd switches in a same function, e.g.
        //switch(cmd){case 0: ...; case 1: ...;} ... switch(cmd){case 2: .X.; case 3: .Y.;}
        //If we want to reach X, the previous analysis may tell us case 0 and 1 will lead to X since it's the successor
        //of the previous "switch", while in fact we should exclude case 0 and 1 (i.e. block the leading cmds here) and only reserve case 2.
        //TODO 1:
        //switch(cmd) {...}
        //switch(cmd) {case 0:case 1:case 2: .X.;} //(1) no default case, (2) all other cases share the same handler code
        //"X" does belong to the 2nd switch exclusively, but our current algorithm will regard it as a shared exit...
        //In this situation we will be unable to exclude the reaching cmds, causing burdens for the fuzzer, but at least it's safe (no cmds are overlooked.)
        //TODO 2:
        //If we want to reach a default case handler, we should say "specify a cmd that doesn't have a dedicated handler", instead of "any cmd is ok"
        std::set<BasicBlock*> *shared_bbs = this->get_shared_switch_bbs(&I); 
        for (BasicBlock *cur_bb : this->uniq_bb_map[&I]) {
            //For each succ bb exclusively belonging to current switch-case IR, block out all previous reaching cmds.
            this->currState.switchMap[cur_bb].clear(); 
        }
        //Ok, now set the cmd map for this switch IR.
        for (auto c : I.cases()){
            ConstantInt *val = c.getCaseValue();
            //int64_t c_val = val->getSExtValue();
            uint64_t c_val = val->getZExtValue();
            BasicBlock *bb = c.getCaseSuccessor();
#ifdef DEBUG_VISIT_SWITCH_INST
            dbgs() << "Cond Val: " << c_val;
            dbgs() << " Dst BB: " << bb->getName().str() << "\n";
#endif
            this->has_explicit_cmd = true;
            //Add the case successors to the map.
            std::set<BasicBlock*> *succs = this->get_all_successors(bb);
            for(BasicBlock *succ_bb : *succs){
                this->currState.switchMap[succ_bb].insert(c_val);
            }
        }
    }

    std::set<BasicBlock*>* SwitchAnalysisVisitor::get_shared_switch_bbs(SwitchInst *I) {
        if (!I) {
            return nullptr;
        }
        if (this->shared_bb_map.find(I) != this->shared_bb_map.end()) {
            return &this->shared_bb_map[I];
        }
        this->uniq_bb_map[I].clear();
        BasicBlock *def_bb = I->getDefaultDest();
        bool inited = true;
        if (def_bb) {
            std::set<BasicBlock*> *def_succs = this->get_all_successors(def_bb);
            this->shared_bb_map[I] = *def_succs;
            this->uniq_bb_map[I] = *def_succs;
        }else {
            inited = false;
        }
        for(auto c : I->cases()){
            BasicBlock *bb = c.getCaseSuccessor();
            std::set<BasicBlock*> *succs = this->get_all_successors(bb);
            this->uniq_bb_map[I].insert(succs->begin(),succs->end());
            if (!inited) {
                this->shared_bb_map[I] = *succs;
                inited = true;
            }else {
                std::set<BasicBlock*> intersect;
                std::set_intersection(succs->begin(),succs->end(),this->shared_bb_map[I].begin(),this->shared_bb_map[I].end(),
                                  std::inserter(intersect,intersect.begin()));
                this->shared_bb_map[I].clear();
                this->shared_bb_map[I].insert(intersect.begin(),intersect.end());
            }
        }
        std::set<BasicBlock*> diff;
        std::set_difference(this->uniq_bb_map[I].begin(),this->uniq_bb_map[I].end(),this->shared_bb_map[I].begin(),this->shared_bb_map[I].end(),
                          std::inserter(diff,diff.begin()));
        this->uniq_bb_map[I].clear();
        this->uniq_bb_map[I].insert(diff.begin(),diff.end());
        return &this->shared_bb_map[I];
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
        //inclusive
        this->succ_map[bb].insert(bb);
        return &this->succ_map[bb];
    }

    void SwitchAnalysisVisitor::visit(BasicBlock *BB) {
    }

    //Sometimes "cmd" and correlated handler procedure can be stored in an array, thus in the main "ioctl" the handler will be
    //indirectly called by looking up the "cmd" in the array, we want to handle this case here by using some heuristics.
    void SwitchAnalysisVisitor::resolveImplicitCMD(CallInst &I, Function *currFunc, std::vector<Instruction *> *callSiteContext) {
        if (!currFunc || !callSiteContext) {
            return;
        }
        BasicBlock *bb = callSiteContext->back()->getParent();
        if (!bb) {
            return;
        }
        //First, this needs to be an indirect call..
        Function *calledFunc = I.getCalledFunction();
        if (calledFunc != nullptr) {
            //An explicit call inst, impossible to involve implicit cmd.
            return;
        }
#ifdef DEBUG_RESOLVE_IMPLICIT_CMD
        dbgs() << "SwitchAnalysisVisitor::resolveImplicitCMD: Analyze the indirect callee: " << currFunc->getName().str() << " @ INST: " << InstructionUtils::getValueStr(&I) << "\n"; 
#endif
        //Second, our heuristic is that the indirect target callee (currFunc) should reside in a const aggregate, which then reside
        //in a const array/vector, e.g.
        //[ {0, handler0}, {1, handler1}, ... ]
        std::map<ConstantAggregate*,std::set<long>> *func_uses = InstructionUtils::getUsesInStruct(currFunc);
        if (!func_uses) {
            return;
        }
        for (auto& x : *func_uses) {
            ConstantAggregate *constA = x.first;
#ifdef DEBUG_RESOLVE_IMPLICIT_CMD
            dbgs() << "SwitchAnalysisVisitor::resolveImplicitCMD: USE: " << InstructionUtils::getValueStr(constA) << "\n";
#endif
            //Is it used in an array/vector?
            bool in_array = false;
            for (Value::user_iterator i = constA->user_begin(), e = constA->user_end(); i != e; ++i) {
                ConstantArray *constArr = dyn_cast<ConstantArray>(*i);
                ConstantVector *constV = dyn_cast<ConstantVector>(*i);
                if (!constArr && !constV) {
                    continue;
                }
                in_array = true;
                break;
            }
            if (!in_array) {
#ifdef DEBUG_RESOLVE_IMPLICIT_CMD
                dbgs() << "SwitchAnalysisVisitor::resolveImplicitCMD: Not in an array/vector.\n";
#endif
                continue;
            }
            //Ok, it seems to be a jump table, while we still need to see whether the struct contains a "cmd" field.
            for (unsigned c = 0; c < constA->getNumOperands(); ++c) {
                Constant *constF = constA->getAggregateElement(c);
                ConstantInt *constI = dyn_cast<ConstantInt>(constF);
                if (!constI) {
                    continue;
                }
                //TODO: our current assumption is that the first integer in the struct is the "cmd".
                uint64_t c_val = constI->getZExtValue();
                this->currState.switchMap[bb].insert(c_val);
#ifdef DEBUG_RESOLVE_IMPLICIT_CMD
                dbgs() << "SwitchAnalysisVisitor::resolveImplicitCMD: Relate cmd: " << c_val << " to func: " << currFunc->getName().str() << "\n"; 
                dbgs() << "BB in function: " << bb->getParent()->getName().str() << "\n";
#endif
                return;
            }
#ifdef DEBUG_RESOLVE_IMPLICIT_CMD
            dbgs() << "SwitchAnalysisVisitor::resolveImplicitCMD: No integer field.\n";
#endif
        }
        return;
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
#ifdef RESOLVE_IMPLICIT_CMD
        if (!this->has_explicit_cmd) {
            this->resolveImplicitCMD(I,currFunc,callSiteContext);
        }
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
