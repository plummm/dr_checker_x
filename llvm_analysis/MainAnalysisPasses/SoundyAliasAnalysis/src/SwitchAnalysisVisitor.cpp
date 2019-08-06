//
// Created by hz on 4/25/19.
//

#include "SwitchAnalysisVisitor.h"
#include "InstructionUtils.h"

using namespace llvm;
namespace DRCHECKER {

    //#define DEBUG_CALL_INST
    //#define DEBUG_VISIT_SWITCH_INST
    #define RESOLVE_IMPLICIT_CMD
    #define DEBUG_RESOLVE_IMPLICIT_CMD
    //TODO: we cannot guarantee this magic number will not appear as a valid case number...
    #define DEFAULT_CASE_NUM 88888888

    bool SwitchAnalysisVisitor::is_cmd_switch(SwitchInst &I) {
        Value *cond_var = I.getCondition();
        if ((!cond_var) || cond_var->getName().empty()) {
            return false;
        }
        std::string cond_name = cond_var->getName().str();
        if (cond_name != "cmd" && cond_name != "cmd_in") {
            return false;
        }
        return true;
    }

    void SwitchAnalysisVisitor::visitSwitchInst(SwitchInst &I) {
        //TODO: do not process SwitchInst that we have already processed.
#ifdef DEBUG_VISIT_SWITCH_INST
        dbgs() << "SwitchAnalysisVisitor::visitSwitchInst: \n";
        InstructionUtils::printInst(&I,dbgs());
#endif
        //Make sure that the switch variable is the "cmd" arg.
        if (!this->is_cmd_switch(I)) {
            return;
        }
        Value *cond_var = I.getCondition();
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
            std::set<BasicBlock*> *succs = new std::set<BasicBlock*>();
            this->get_case_successors(bb,c_val,succs);
            for(BasicBlock *succ_bb : *succs){
                this->currState.switchMap[succ_bb].insert(c_val);
            }
            delete(succs);
        }
        //We also need to consider: which BBs can be or only be reached w/ a default case number.
        std::set<BasicBlock*> *def_succs = new std::set<BasicBlock*>();
        this->get_case_successors(def_bb,DEFAULT_CASE_NUM,def_succs);
        for(BasicBlock *succ_bb : *def_succs){
            this->currState.switchMap[succ_bb].insert(DEFAULT_CASE_NUM);
        }
        delete(def_succs);
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

    //NOTE: this will be inclusive (the successor list also contains the root BB.)
    void SwitchAnalysisVisitor::_get_all_successors(BasicBlock *bb, std::set<BasicBlock*> &res) {
        if (!bb || res.find(bb) != res.end()) {
            return;
        }
        //A result cache.
        if (this->succ_map.find(bb) != this->succ_map.end()) {
            res.insert(this->succ_map[bb].begin(),this->succ_map[bb].end());
            return;
        }
        //inclusive
        res.insert(bb);
        for (llvm::succ_iterator sit = llvm::succ_begin(bb), set = llvm::succ_end(bb); sit != set; ++sit) {
            this->_get_all_successors(*sit,res);
        }
        return;
    }

    //NOTE: this will be inclusive (the successor list also contains the root BB.)
    std::set<BasicBlock*> *SwitchAnalysisVisitor::get_all_successors(BasicBlock *bb) {
        if (!bb) {
            return nullptr;
        }
        //A result cache.
        if (this->succ_map.find(bb) != this->succ_map.end()) {
            return &this->succ_map[bb];
        }
        std::set<BasicBlock*> res;
        res.clear();
        this->_get_all_successors(bb,res);
        this->succ_map[bb] = res;
        return &this->succ_map[bb];
    }

    //Get all successors of a basicblock, w/ a certain "cmd" value.
    //NOTE: for now we don't cache the results, as SwitchAnalysis will run only once for each switch inst.
    void SwitchAnalysisVisitor::get_case_successors(BasicBlock *bb, uint64_t cn, std::set<BasicBlock*> *res) {
        if (!bb || !res) {
            return;
        }
        if (res->find(bb) != res->end()) {
            //We have already visited this bb (i.e. loop) or it's currently being processed.
            return;
        }
#ifdef DEBUG_VISIT_SWITCH_INST
        dbgs() << "get_case_successors,BB: " << InstructionUtils::getBBStrID(bb) << "/" << InstructionUtils::getBBStrID_No(bb) << " cn: " << cn << "\n";
#endif
        //inclusive
        res->insert(bb);
        //Does current BB end with a switch-case inst?
        Instruction *tinst = bb->getTerminator();
        if (tinst && dyn_cast<SwitchInst>(tinst)) {
            //A switch inst, we need to follow the specified "cmd".
            SwitchInst *sinst = dyn_cast<SwitchInst>(tinst);
            //make sure the switch is regarding the "cmd"
            if (this->is_cmd_switch(*sinst)) {
                for (auto c : sinst->cases()){
                    ConstantInt *val = c.getCaseValue();
                    //int64_t c_val = val->getSExtValue();
                    uint64_t c_val = val->getZExtValue();
                    if (c_val == cn) {
                        BasicBlock *case_bb = c.getCaseSuccessor();
                        this->get_case_successors(case_bb,cn,res);
                        return;
                    }
                }
                //This means, we have to take the default exit of this switch-case since no case matches the specified cmd value.
                BasicBlock *def_dest = sinst->getDefaultDest();
                this->get_case_successors(def_dest,cn,res);
                return;
            }
        }
        //TODO: any non-switch comparison with cmd like if (cmd == XXX) ?
        //Recursively deal with every direct successor.
        for(succ_iterator sit = succ_begin(bb), set = succ_end(bb); sit != set; ++sit) {
            BasicBlock *curr_bb = *sit;
            this->get_case_successors(curr_bb,cn,res);
        }
        return;
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

    //Count the #BB of each branch of the branch inst.
    void SwitchAnalysisVisitor::visitBranchInst(BranchInst &I) {
        //
    }

}// namespace DRCHECKER
