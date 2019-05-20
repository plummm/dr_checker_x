//
// Created by hz on 4/5/19.
//

#include "ModAnalysisVisitor.h"
#include "PointsToUtils.h"
#include "TaintUtils.h"
#include "TaintInfo.h"
#include "../../Utils/include/InstructionUtils.h"

using namespace llvm;
namespace DRCHECKER {

    //#define DEBUG_STORE_INST
    //#define DEBUG_CALL_INST
    #define DEBUG_MOD_TRAIT
    #define DEBUG_BR_TRAIT
    #define DEBUG_NLP
    //#define DEBUG_TMP

    void ModAnalysisVisitor::visitStoreInst(StoreInst &I) {
#ifdef DEBUG_TMP
        dbgs() << "ModAnalysisVisitor::visitStoreInst(): ";
        I.print(dbgs());
        dbgs() << "\n";
#endif
        //Get the dst pointer of the "store".
        Value *dstPointer = I.getPointerOperand();
        //Strip if necessary.
        if(!PointsToUtils::hasPointsToObjects(this->currState, this->currFuncCallSites, dstPointer)) {
            dstPointer = dstPointer->stripPointerCasts();
        }
        //Get its points-to set.
        std::set<PointerPointsTo*>* dstPointsTo = PointsToUtils::getPointsToObjects(this->currState,
                                                                                    this->currFuncCallSites,
                                                                                    dstPointer);
        if(dstPointsTo == nullptr) {
#ifdef DEBUG_STORE_INST
            dbgs() << "ModAnalysisVisitor::visitStoreInst(): No points-to info: ";
            I.print(dbgs());
            dbgs() << "\n";
#endif
            return;
        }

#ifdef DEBUG_STORE_INST
        dbgs() << "ModAnalysisVisitor::visitStoreInst(): See whether the dst pointer points to any taint-src objects...\n";
#endif
        //Does it point to any taint-src objects (e.g. global objects and outside objects) ?
        //Target global states to modify.
        std::set<std::pair<long, AliasObject*>> targetObjects;
        for (PointerPointsTo *currPointsToObj:*dstPointsTo) {
            long target_field = currPointsToObj->dstfieldId;
            AliasObject *dstObj = currPointsToObj->targetObject;
            if (!dstObj || !dstObj->is_taint_src){
                continue;
            }
            auto to_check = std::make_pair(target_field, dstObj);
            if(std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                targetObjects.insert(targetObjects.end(), to_check);
            }
#ifdef DEBUG_STORE_INST
            dbgs() << "ModAnalysisVisitor::visitStoreInst(): Found one taint-src objects!\n";
#endif
            //Ok, the dst pointer points to a taint-src object, which means current "store"
            //instruction can potentially modify a global state.
            //We need to record current store instruction to the correlated taint tag.
            std::set<TaintFlag*> *fieldTaint = dstObj->getFieldTaintInfo(target_field);
            if(fieldTaint != nullptr) {
                for(auto existingTaint:*fieldTaint) {
                    if (existingTaint && existingTaint->tag){
                        TaintTag *tag = existingTaint->tag;
                        //We should only record the mod inst to the original taint tag of the taint src object. 
                        if (tag->v != dstObj->getValue() || tag->fieldId != target_field) {
                            continue;
                        }
                        //Record current instruction in the tag mod inst list.
#ifdef DEBUG_STORE_INST
                        dbgs() << "Add to mod_inst_list (fieldTaint): ";
                        I.print(dbgs());
                        dbgs() << "\n";
                        tag->dumpInfo(dbgs());
#endif
                        tag->insertModInst(&I,this->actx->callSites);
                    }
                }
            } else {
                //We have no taint flags for the individual fields, is this possible???
                //Anyway, try to record the instruction in the shared taint flag then.
                if(dstObj->all_contents_tainted) {
                    //assert(this->all_contents_taint_flag != nullptr);
                    if (!dstObj->all_contents_taint_flag){
#ifdef DEBUG_STORE_INST
                        dbgs() << "ModAnalysisVisitor::visitStoreInst(): No all_contents_taint_flag!!\n";
#endif
                        continue;
                    }
                    if (!dstObj->all_contents_taint_flag->tag){
#ifdef DEBUG_STORE_INST
                        dbgs() << "ModAnalysisVisitor::visitStoreInst(): No tag in all_contents_taint_flag!!\n";
#endif
                        continue;
                    }
#ifdef DEBUG_STORE_INST
                    dbgs() << "Add to mod_inst_list (all_contents_taint_flag): ";
                    I.print(dbgs());
                    dbgs() << "\n";
#endif
                    dstObj->all_contents_taint_flag->tag->insertModInst(&I,this->actx->callSites);
                }
            }
        }
        //Analyze the update pattern.
        if (!targetObjects.empty()) {
            this->analyzeModPattern(I, &targetObjects);
        }
        return;
    }

    //Analyze the modification pattern of current "store", e.g., a = 1 or a++?
    void ModAnalysisVisitor::analyzeModPattern(StoreInst &I, std::set<std::pair<long, AliasObject*>> *targetObjects) {
#ifdef DEBUG_MOD_TRAIT
        dbgs() << "ModAnalysisVisitor::analyzeModPattern: ";
        I.print(dbgs());
        dbgs() << "\n";
#endif
        if ( this->currState.modTraitMap.find(&I) != this->currState.modTraitMap.end() &&
             this->currState.modTraitMap[&I].find(this->actx->callSites) != this->currState.modTraitMap[&I].end() ) 
        {
            //Already analyzed
            return;
        }
        //GlobalState &currState;
        Value *srcValue = I.getValueOperand();
        //For now let's only consider the scalar values to store.
        if (!InstructionUtils::isScalar(srcValue)) {
#ifdef DEBUG_MOD_TRAIT
            dbgs() << "ModAnalysisVisitor::analyzeModPattern: The value to store is not a scalar\n";
#endif
            return;
        }
        //Is it a const value?
        if (dyn_cast<llvm::Constant>(srcValue)) {
            //A direct assignment.
            int r = InstructionUtils::getConstantValue(dyn_cast<llvm::Constant>(srcValue), &this->currState.modTraitMap[&I][this->actx->callSites]);
#ifdef DEBUG_MOD_TRAIT
            dbgs() << "ModAnalysisVisitor::analyzeModPattern: The value to store is a constant: ";
            for (auto& x : this->currState.modTraitMap[&I][this->actx->callSites]) {
                dbgs() << x.first << ":" << x.second << " ";
            }
            dbgs() << "\n";
#endif
            return;
        }
        //Ok, it's not an const value, then how is it derived?
        //Note that in this situation, there can be two cases:
        //(1) the variable to store is derived from some other non-relavent (to the global state) variables (e.g. func arg),
        //so basically we cannot get the exact value to store, we rely on fuzzing to hit the proper value here.
        //(2) the modification is based on the global state itself, e.g., a self addition.
        //We only try to match (2) here, which needs the "targetObjects" information.
        if ((!targetObjects) || targetObjects->empty()) {
            return;
        }
        //First let's skip all potential cast instructions after the arithmetic instruction.
        srcValue = InstructionUtils::stripAllCasts(srcValue,true);
        if (!srcValue) {
            //Maybe the origin is a pointer instead of a scalar, what else can cause this?
#ifdef DEBUG_MOD_TRAIT
            dbgs() << "ModAnalysisVisitor::analyzeModPattern: Null after strip all casts (for scalar)\n";
#endif
            return;
        }
        //NOTE: we assume that the current "srcValue" is the arithmetics inst we want to analyze. 
        //TODO: phi node
        int64_t cn, cn_o;
        //TODO: the analysis should be per-taint-tag, but now we consider all "targetObjects" together 
        //(i.e. load & store may both belong to "targetObjects" but not the same one)
        if (!this->verifyPatternExistence(srcValue,targetObjects,&cn,&cn_o)) {
            //No recognizable patterns.
#ifdef DEBUG_MOD_TRAIT
            dbgs() << "ModAnalysisVisitor::analyzeModPattern: unrecognized pattern!\n";
#endif
            return;
        }
        //Next figure out the arithmetics.
        int r = this->getArithmeticsInf(srcValue,&this->currState.modTraitMap[&I][this->actx->callSites],cn,cn_o);
#ifdef DEBUG_MOD_TRAIT
        dbgs() << "ModAnalysisVisitor::analyzeModPattern: After getArithmeticsInf: ";
            for (auto& x : this->currState.modTraitMap[&I][this->actx->callSites]) {
                dbgs() << x.first << ":" << x.second << " ";
            }
            dbgs() << "\n";
#endif
        return;
    }
    
    int ModAnalysisVisitor::verifyPatternExistence(Value* v, std::set<std::pair<long, AliasObject*>> *targetObjects, int64_t *cn, int64_t *cn_o) {
        if (!v || !dyn_cast<llvm::User>(v)) {
            return 0;
        }
#ifdef DEBUG_MOD_TRAIT
        dbgs() << "ModAnalysisVisitor::verifyPatternExistence: ";
        v->print(dbgs());
        dbgs() << "\n";
#endif
        llvm::User *u = dyn_cast<llvm::User>(v);
        //We currently match the pattern "x op C" where C is a contant and x is the global state.
        //That's to say, the inst should have two operands.
        if (u->getNumOperands() != 2) {
            return 0;
        }
        llvm::Value* op[2];
        op[0] = u->getOperand(0);
        op[1] = u->getOperand(1);
        if ((!dyn_cast<llvm::Constant>(op[0])) == (!dyn_cast<llvm::Constant>(op[1]))) {
            //both operands are (not) constants, we cannot recognize such patterns now.
#ifdef DEBUG_MOD_TRAIT
            dbgs() << "ModAnalysisVisitor::verifyPatternExistence: both/neither operands are constants.\n";
#endif
            return 0;
        }
        std::map<std::string,int64_t> m;
        int r;
        int tainted_by_target = 0;
        for (int i=0; i<2; i++) {
            if (dyn_cast<llvm::Constant>(op[i])) {
                //Ok get the constant value.
                r = InstructionUtils::getConstantValue(dyn_cast<llvm::Constant>(op[i]),&m);
                (*cn_o) = i;
                if (m.find("CONST_INT") != m.end()) {
                    (*cn) = m["CONST_INT"];
                }else {
                    //TODO: We don't match these patterns now.
#ifdef DEBUG_MOD_TRAIT
                    dbgs() << "ModAnalysisVisitor::verifyPatternExistence: the contant is not CONST_INT.\n";
#endif
                    return 0;
                }
            } /*constant op*/ else {
                //Decide whether the varible is indeed the global state, otherwise we cannot match the pattern.
                //We can do this in two ways:
                //(1) Simply see whether the variable is tainted by any combination in "targetObjects".
                //(2) Trace back the IR and match the pattern "load x, obj->f; [cast...] ; arithmeticis"
                //TODO: we now use (1)
                std::set<TaintFlag*>* taintFlags = TaintUtils::getTaintInfo(this->currState, this->currFuncCallSites, op[i]);
                if (!taintFlags) {
#ifdef DEBUG_MOD_TRAIT
                    dbgs() << "ModAnalysisVisitor::verifyPatternExistence: the variable is not tainted.\n";
#endif
                    return 0;
                }
                for(auto tf : *taintFlags) {
                    if (!tf || !tf->tag) {
                        continue;
                    }
                    TaintTag *tag = tf->tag;
                    for (auto to : *targetObjects) {
                        if (tag->v == to.second->getValue() && tag->fieldId == to.first) {
                            tainted_by_target = 1;
                            break;
                        }
                    }//Check whether it's in "targetObjects"
                    if (tainted_by_target) {
                        break;
                    }
                }
            } //variable op
        }//for
        //Reaching here, we must have already got the constant number, thus the final result is decided by
        //whether the variable is from the global state.
#ifdef DEBUG_MOD_TRAIT
        dbgs() << "ModAnalysisVisitor::verifyPatternExistence: tainted_by_target: " << tainted_by_target << "\n";
#endif
        return tainted_by_target;
    }

    //Idealy, we want to get the full formula of the variable to store, which requires baiscally a backward slicing
    //and semantic analysis of each instruction in the slice. However, here what we actually do is a simple
    //light-weight pattern (like "a++") match for just the last arithmetics instruction.
    int ModAnalysisVisitor::getArithmeticsInf(Value* v, TRAIT* res, int64_t cn, int64_t cn_o) {
        if (!v || !res) {
            return 0;
        }
        //It's time to analyze the opcode.
        if (dyn_cast<llvm::BinaryOperator>(v)) {
            llvm::BinaryOperator *binop = dyn_cast<llvm::BinaryOperator>(v);
            llvm::Instruction::BinaryOps opc = binop->getOpcode();
            switch(opc) {
                case llvm::Instruction::BinaryOps::Add:
                case llvm::Instruction::BinaryOps::FAdd:
                    (*res)["ADD"] = cn;
                    break;
                case llvm::Instruction::BinaryOps::Sub:
                case llvm::Instruction::BinaryOps::FSub:
                    if (cn_o == 1) {
                        (*res)["SUB"] = cn;
                    }
                    break;
                case llvm::Instruction::BinaryOps::Mul:
                case llvm::Instruction::BinaryOps::FMul:
                    (*res)["MUL"] = cn;
                    break;
                case llvm::Instruction::BinaryOps::UDiv:
                case llvm::Instruction::BinaryOps::SDiv:
                case llvm::Instruction::BinaryOps::FDiv:
                    if (cn_o == 1) {
                        (*res)["DIV"] = cn;
                    }
                    break;
                case llvm::Instruction::BinaryOps::URem:
                case llvm::Instruction::BinaryOps::SRem:
                case llvm::Instruction::BinaryOps::FRem:
                    if (cn_o == 1) {
                        (*res)["REM"] = cn;
                    }
                    break;
                case llvm::Instruction::BinaryOps::Shl:
                    if (cn_o == 1) {
                        (*res)["SHL"] = cn;
                    }
                    break;
                case llvm::Instruction::BinaryOps::LShr:
                case llvm::Instruction::BinaryOps::AShr:
                    if (cn_o == 1) {
                        (*res)["SHR"] = cn;
                    }
                    break;
                case llvm::Instruction::BinaryOps::And:
                    (*res)["AND"] = cn;
                    break;
                case llvm::Instruction::BinaryOps::Or:
                    (*res)["OR"] = cn;
                    break;
                case llvm::Instruction::BinaryOps::Xor:
                    (*res)["XOR"] = cn;
                    break;
                default:
                    break;
            }
        }else if (dyn_cast<llvm::OverflowingBinaryOperator>(v)) {
            if (dyn_cast<llvm::AddOperator>(v)) {
                (*res)["ADD"] = cn;
            }else if (dyn_cast<llvm::MulOperator>(v)) {
                (*res)["MUL"] = cn;
            }else if (dyn_cast<llvm::ShlOperator>(v)) {
                if (cn_o == 1) {
                    (*res)["SHL"] = cn;
                }
            }else if (dyn_cast<llvm::SubOperator>(v)) {
                if (cn_o == 1) {
                    (*res)["SUB"] = cn;
                }
            }
        }else if (dyn_cast<llvm::PossiblyExactOperator>(v)) {
            if (dyn_cast<llvm::AShrOperator>(v) || dyn_cast<llvm::LShrOperator>(v)) {
                if (cn_o == 1) {
                    (*res)["SHR"] = cn;
                }
            }else if (dyn_cast<llvm::SDivOperator>(v) || dyn_cast<llvm::UDivOperator>(v)) {
                if (cn_o == 1) {
                    (*res)["DIV"] = cn;
                }
            }
        }else {
            //TODO: What else?
        }
        return 1;
    }

    //Try to get the read pattern of the GV in the branch condition, e.g., a == 0 or a > 1?
    void ModAnalysisVisitor::visitBranchInst(BranchInst &I) {
#ifdef DEBUG_BR_TRAIT
        dbgs() << "ModAnalysisVisitor::visitBranchInst: ";
        I.print(dbgs());
        dbgs() << "\n";
#endif
        //First figure out whether this br is tainted, no need to analyze untainted br.
        std::set<TaintFlag*>* taintFlags = TaintUtils::getTaintInfo(this->currState, this->currFuncCallSites, &I);
        if ((!taintFlags) || taintFlags->empty()) {
#ifdef DEBUG_BR_TRAIT
            dbgs() << "ModAnalysisVisitor::visitBranchInst: Not tainted.\n";
#endif
            return;
        }
        //Try to identify the condition pattern.
        //The general pattern we handle:
        //<cond> = cmp ......
        //br i1 <cond>, label <iftrue>, label <iffalse>
        Value *condition = I.getCondition();
        if (!condition || !dyn_cast<CmpInst>(condition)) {
#ifdef DEBUG_BR_TRAIT
            dbgs() << "ModAnalysisVisitor::visitBranchInst: the condition is not from cmp inst\n";
#endif
            return;
        }
        CmpInst *cmpInst = dyn_cast<CmpInst>(condition);
        //TODO: we now only consider the case where one op is a variable while the other is a constant.
        if ((!dyn_cast<Constant>(cmpInst->getOperand(0))) == (!dyn_cast<Constant>(cmpInst->getOperand(1)))) {
#ifdef DEBUG_BR_TRAIT
            dbgs() << "ModAnalysisVisitor::visitBranchInst: the cmp inst operands are both/neither constants.\n";
#endif
            return;
        }
        int cn_o;
        Constant *c;
        for (int i=0; i<2; ++i) {
            if (dyn_cast<Constant>(cmpInst->getOperand(i))) {
                cn_o = i;
                c = dyn_cast<Constant>(cmpInst->getOperand(i));
                break;
            }
        }
        TRAIT *pt = &this->currState.brTraitMap[&I][this->actx->callSites];
        //Is the comparison against a function return value?
        ///////////////////////////////////////////////////
        Value *v = cmpInst->getOperand(1-cn_o);
        v = InstructionUtils::stripAllCasts(v,false);
        if (v && dyn_cast<CallInst>(v)) {
            std::string callee = InstructionUtils::getCalleeName(dyn_cast<CallInst>(v),true);
            if (callee.size() > 0){
#ifdef DEBUG_NLP
                dbgs() << "ModAnalysisVisitor::visitBranchInst: condition related to callee: " << callee << "\n";
#endif
                (*pt)["RET_" + callee] = 0;
                //TODO: in this case need we return?
            }
        }
        ///////////////////////////////////////////////////
        std::map<std::string,int64_t> m;
        int r = InstructionUtils::getConstantValue(c,&m);
        int cn;
        if (m.find("CONST_INT") != m.end()) {
            cn = m["CONST_INT"];
        }else {
            //TODO: We don't match these patterns now.
#ifdef DEBUG_BR_TRAIT
            dbgs() << "ModAnalysisVisitor::visitBranchInst: the cmp inst constant operand is not CONST_INT\n";
#endif
            return;
        }
        //Figure out its predicate.
        llvm::CmpInst::Predicate pred = cmpInst->getPredicate();
        switch(pred) {
            case llvm::CmpInst::Predicate::FCMP_OEQ:
            case llvm::CmpInst::Predicate::FCMP_UEQ:
            case llvm::CmpInst::Predicate::ICMP_EQ:
                (*pt)["=="] = cn;
                break;
            case llvm::CmpInst::Predicate::FCMP_OGT:
            case llvm::CmpInst::Predicate::FCMP_UGT:
            case llvm::CmpInst::Predicate::ICMP_UGT:
            case llvm::CmpInst::Predicate::ICMP_SGT:
            case llvm::CmpInst::Predicate::FCMP_OGE:
            case llvm::CmpInst::Predicate::FCMP_UGE:
            case llvm::CmpInst::Predicate::ICMP_UGE:
            case llvm::CmpInst::Predicate::ICMP_SGE:
                if (cn_o == 1) {
                    (*pt)[">="] = cn;
                }else {
                    (*pt)["<="] = cn;
                }
                break;
            case llvm::CmpInst::Predicate::FCMP_OLT:
            case llvm::CmpInst::Predicate::FCMP_ULT:
            case llvm::CmpInst::Predicate::ICMP_ULT:
            case llvm::CmpInst::Predicate::ICMP_SLT:
            case llvm::CmpInst::Predicate::FCMP_OLE:
            case llvm::CmpInst::Predicate::FCMP_ULE:
            case llvm::CmpInst::Predicate::ICMP_ULE:
            case llvm::CmpInst::Predicate::ICMP_SLE:
                if (cn_o == 1) {
                    (*pt)["<="] = cn;
                }else {
                    (*pt)[">="] = cn;
                }
                break;
            case llvm::CmpInst::Predicate::FCMP_ONE:
            case llvm::CmpInst::Predicate::FCMP_UNE:
            case llvm::CmpInst::Predicate::ICMP_NE:
                (*pt)["!="] = cn;
                break;
            case llvm::CmpInst::Predicate::FCMP_TRUE:
                //
            case llvm::CmpInst::Predicate::FCMP_FALSE:
                //
            case llvm::CmpInst::Predicate::FCMP_ORD:
                //
            case llvm::CmpInst::Predicate::FCMP_UNO:
                //
            default:
                break;
        }
#ifdef DEBUG_BR_TRAIT
        dbgs() << "ModAnalysisVisitor::visitBranchInst: the traits: ";
        for (auto& x : *pt) {
            dbgs() << x.first << ":" << x.second << " ";
        }
        dbgs() << "\n";
#endif
        return;
    }

    VisitorCallback* ModAnalysisVisitor::visitCallInst(CallInst &I, Function *currFunc,
                                                         std::vector<Instruction *> *oldFuncCallSites,
                                                         std::vector<Instruction *> *callSiteContext) {
#ifdef DEBUG_CALL_INST
       dbgs() << "---------\nMod analysis visits call instruction: ";
       I.print(dbgs());
       dbgs() << "\n";
#endif
       std::string n = InstructionUtils::getCalleeName(&I,true);
       if (n.size() > 0) {
#ifdef DEBUG_NLP
           dbgs() << "ModAnalysisVisitor::visitCallInst: callee inst: " << n << "\n";
#endif
           this->currState.calleeMap[n][&I].insert(this->actx->callSites);
       }
       // if this is a kernel internal function.
       if(currFunc->isDeclaration()) {
           //this->handleKernelInternalFunction(I, currFunc);
           return nullptr;
       }
       // create a new ModAnalysisVisitor
       ModAnalysisVisitor *vis = new ModAnalysisVisitor(currState, currFunc, callSiteContext);

       return vis;
    }

}// namespace DRCHECKER
