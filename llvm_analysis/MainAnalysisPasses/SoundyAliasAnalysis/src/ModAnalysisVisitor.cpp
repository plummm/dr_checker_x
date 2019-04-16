//
// Created by hz on 4/5/19.
//

#include "ModAnalysisVisitor.h"
#include "PointsToUtils.h"
#include "TaintUtils.h"
#include "TaintInfo.h"

using namespace llvm;
namespace DRCHECKER {

    #define DEBUG_STORE_INST
    //#define DEBUG_CALL_INST
    #define DEBUG_TMP

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
        for (PointerPointsTo *currPointsToObj:*dstPointsTo) {
            long target_field = currPointsToObj->dstfieldId;
            AliasObject *dstObj = currPointsToObj->targetObject;
            if (!dstObj || !dstObj->is_taint_src){
                continue;
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
#endif
                        tag->insertModInst(&I,this->currFuncCallSites);
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
                    dstObj->all_contents_taint_flag->tag->insertModInst(&I,this->currFuncCallSites);
                }
            }
        }
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
