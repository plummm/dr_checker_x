//
// Created by machiry on 12/5/16.
//

#include "TaintAnalysisVisitor.h"
#include "PointsToUtils.h"
#include "TaintUtils.h"

using namespace llvm;
namespace DRCHECKER {

//#define DEBUG_CALL_INSTR
//#define DEBUG_RET_INSTR
//#define DEBUG_LOAD_INSTR
//#define DEBUG_CAST_INSTR
//#define DEBUG
//#define DEBUG_BIN_INSTR
#define ENFORCE_TAINT_PATH
//#define DEBUG_ENFORCE_TAINT_PATH
#define DEBUG_STORE_INSTR_MAPPING

    InstLoc *TaintAnalysisVisitor::makeInstLoc(Value *v) {
        return new InstLoc(v,this->currFuncCallSites);
    }

    std::set<TaintFlag*>* TaintAnalysisVisitor::getTaintInfo(Value *targetVal) {
        return TaintUtils::getTaintInfo(this->currState, this->currFuncCallSites, targetVal);
    }

    //"I" is the inst site where need the ptr taint info. 
    void TaintAnalysisVisitor::getPtrTaintInfo(Value *targetVal, std::set<TaintFlag*> &retTaintFlag, Instruction *I) {
        std::set<PointerPointsTo*> currValPointsTo;
        std::set<PointerPointsTo*> *currPtsTo = PointsToUtils::getPointsToObjects(this->currState, this->currFuncCallSites, targetVal);
        if(currPtsTo != nullptr) {
            currValPointsTo.insert(currPtsTo->begin(), currPtsTo->end());
        }

        InstLoc *loc = this->makeInstLoc(I);
        for(PointerPointsTo *currPtTo : currValPointsTo) {
            std::set<TaintFlag*> currTaintSet;
            currPtTo->targetObject->getFieldTaintInfo(currPtTo->dstfieldId,currTaintSet,loc);
            if (currTaintSet.size()) {
                for(auto a : currTaintSet) {
                    if(std::find_if(retTaintFlag.begin(), retTaintFlag.end(), [a](const TaintFlag *n) {
                        return  n->isTaintEquals(a);
                    }) == retTaintFlag.end()) {
                        // if not insert the new taint flag into the newTaintInfo.
                        retTaintFlag.insert(a);
                    }
                }
            }
        }
    }

    void TaintAnalysisVisitor::updateTaintInfo(Value *targetVal, std::set<TaintFlag*> *targetTaintInfo) {
        TaintUtils::updateTaintInfo(this->currState, this->currFuncCallSites, targetVal, targetTaintInfo);
    }

    std::set<TaintFlag*>* TaintAnalysisVisitor::makeTaintInfoCopy(Instruction *targetInstruction, std::set<TaintFlag*> *srcTaintInfo, 
                                                                  std::set<TaintFlag*> *dstTaintInfo) {
        if(srcTaintInfo != nullptr) {
            std::set<TaintFlag*> *newTaintInfo = new std::set<TaintFlag*>();
            InstLoc *loc = this->makeInstLoc(targetInstruction);
            bool add_taint = false;
            for (auto currTaint : *srcTaintInfo) {
                if (!currTaint) {
                    continue;
                }
                add_taint = true;
                //hz: we're doing the taint analysis for global states, which can survive function invocations,
                //stmt0 in the 1st function call may affect stmt1 in the 2nd invocation of the same function,
                //although stmt0 cannot reach stmt1 in the CFG of this function, so it seems we should disable the below reachability check.
                //However, we can rely on the post-processing to do the multi-entry fixed-point analysis, and here we still
                //enforce the reachability test to avoid the taint explosion and have a better and cleaner summary of a single entry function.
#ifdef ENFORCE_TAINT_PATH
                if (currTaint->targetInstr != nullptr && !currTaint->is_inherent) {
                    if (targetInstruction) {
                        add_taint = loc->reachable(currTaint->targetInstr);
                    }
                }
#endif
                if(add_taint) {
                    TaintFlag *newTaintFlag = new TaintFlag(currTaint, loc);
                    TaintAnalysisVisitor::addNewTaintFlag(newTaintInfo,newTaintFlag);
                }else {
#ifdef DEBUG_ENFORCE_TAINT_PATH
                    dbgs() << "TaintAnalysisVisitor::makeTaintInfoCopy(): Failed to pass the taint path test, the TaintFlag:\n";
                    currTaint->dumpInfo(dbgs());
                    dbgs() << "Src Inst: ";
                    if (currTaint->targetInstr) {
                        currTaint->targetInstr->print(dbgs());
                    }else {
                        dbgs() << "\n";
                    }
                    dbgs() << "Dst Inst: ";
                    loc->print(dbgs());
#endif
                }
            }
            // if no taint info is propagated.
            if(newTaintInfo->empty()) {
                delete(newTaintInfo);
                delete(loc);
                newTaintInfo = nullptr;
            }
            // if dstTaintInfo is not null.
            if(dstTaintInfo != nullptr && newTaintInfo != nullptr) {
                // copy all the taint info into dstTaintInfo.
                if (dstTaintInfo->empty()) {
                    //No need to check for duplication of existing elements in "dstTaintInfo".
                    dstTaintInfo->insert(newTaintInfo->begin(), newTaintInfo->end());
                }else {
                    for (TaintFlag *tf : *newTaintInfo) {
                        TaintAnalysisVisitor::addNewTaintFlag(dstTaintInfo,tf);
                    }
                }
                // delete new taint info
                delete(newTaintInfo);
                // set return value of dstTaintInfo
                newTaintInfo = dstTaintInfo;
            }
            return newTaintInfo;
        }
        return nullptr;
    }

    std::set<TaintFlag*>* TaintAnalysisVisitor::makeTaintInfoCopy(Instruction *targetInstruction, TaintFlag *srcTaintFlag, 
                                                                  std::set<TaintFlag*> *dstTaintInfo) {
        if (!srcTaintFlag) {
            return nullptr;
        }
        std::set<TaintFlag*> srcTaintInfo;
        srcTaintInfo.insert(srcTaintFlag);
        return TaintAnalysisVisitor::makeTaintInfoCopy(targetInstruction,&srcTaintInfo,dstTaintInfo);
    }

    std::set<TaintFlag*>* TaintAnalysisVisitor::mergeTaintInfo(std::set<Value *> &srcVals, Instruction *targetInstr) {

        std::set<TaintFlag*> *newTaintInfo = new std::set<TaintFlag*>();

        for(auto currVal : srcVals) {
            std::set<TaintFlag*> *currValTaintInfo = getTaintInfo(currVal);
            // we do not have taint info? strip and check
            if(currValTaintInfo == nullptr) {
                currVal = currVal->stripPointerCasts();
                currValTaintInfo = getTaintInfo(currVal);
            }
            if(currValTaintInfo != nullptr) {
                this->makeTaintInfoCopy(targetInstr, currValTaintInfo, newTaintInfo);
            }
        }
        // if there is no taint info?
        if(newTaintInfo->empty()) {
            // delete the object.
            delete(newTaintInfo);
            newTaintInfo = nullptr;
        }
        return newTaintInfo;

    }

    int TaintAnalysisVisitor::addNewTaintFlag(std::set<TaintFlag*> *newTaintInfo, TaintFlag *newTaintFlag) {
        return TaintUtils::addNewTaintFlag(newTaintInfo, newTaintFlag);
    }

    void TaintAnalysisVisitor::visitAllocaInst(AllocaInst &I) {
        // Nothing to do for TaintAnalysis
    }

    void TaintAnalysisVisitor::visitCastInst(CastInst &I) {
        // handles cast instruction.

        // if the src operand is tainted then the instruction is tainted.

        Value *srcOperand = I.getOperand(0);
        std::set<TaintFlag*> *srcTaintInfo = getTaintInfo(srcOperand);
        if(srcTaintInfo == nullptr) {
            srcOperand = srcOperand->stripPointerCasts();
            srcTaintInfo = getTaintInfo(srcOperand);
        }

        // if there exists some taintflags..propagate them
        if(srcTaintInfo != nullptr) {
            std::set<TaintFlag*> *newTaintInfo = this->makeTaintInfoCopy(&I, srcTaintInfo);
            if(newTaintInfo != nullptr) {
                this->updateTaintInfo(&I, newTaintInfo);
            } else {
#ifdef DEBUG_CAST_INSTR
                dbgs() << "Taint Info cannot be propagated because the current instruction is not reachable from";
                dbgs() << "  tainted source at ";
                I.print(dbgs());
                dbgs() << "\n";
#endif
            }
        }

    }

    void TaintAnalysisVisitor::visitBinaryOperator(BinaryOperator &I) {
        // merge taint flag of all the operands.
        std::set<Value*> allVals;
        allVals.insert(allVals.end(), I.getOperand(0));
        allVals.insert(allVals.end(), I.getOperand(1));
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
#ifdef DEBUG_BIN_INSTR
            dbgs() << "Propagating taint in binary instruction\n";
#endif
            updateTaintInfo(&I, newTaintInfo);
        }

    }

    void TaintAnalysisVisitor::visitPHINode(PHINode &I) {
        // get all values that need to be merged.
        std::set<Value*> allVals;
        for(unsigned i=0;i<I.getNumIncomingValues(); i++) {
            allVals.insert(allVals.end(), I.getIncomingValue(i));
        }
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }
    }

    void TaintAnalysisVisitor::visitSelectInst(SelectInst &I) {
        /***
         *  Merge taintinfo of all the objects
         *  reaching this select instruction.
         */
        // get all values that need to be merged.
        std::set<Value*> allVals;
        allVals.insert(allVals.end(), I.getTrueValue());
        allVals.insert(allVals.end(), I.getFalseValue());

        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }

    }

    void TaintAnalysisVisitor::visitGetElementPtrInst(GetElementPtrInst &I) {
        // the GEP instruction always computes pointer, which is used to

        // check if one of the operand is tainted?
        // get all values that need to be merged.
        std::set<Value*> allVals;
        for(unsigned i=0; i<I.getNumOperands(); i++) {
            Value* currOp = I.getOperand(i);
            RangeAnalysis::Range currRange = this->currState.getRange(currOp);
            if(currRange.isBounded()) {
                // if the range of the index we use is bounded?
                // it may not be bad.
                continue;
            }
            allVals.insert(allVals.end(), currOp);
        }
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }
    }

    void TaintAnalysisVisitor::visitLoadInst(LoadInst &I) {
#ifdef DEBUG_LOAD_INSTR
        dbgs() << "TaintAnalysisVisitor::visitLoadInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value *srcPointer = I.getPointerOperand();
        std::set<TaintFlag*> *srcTaintInfo = getTaintInfo(srcPointer);

        std::set<TaintFlag*> *newTaintInfo = new std::set<TaintFlag*>();

        bool already_stripped = true;
        if (srcTaintInfo == nullptr) {
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "TaintAnalysisVisitor::visitLoadInst(): No taint info for srcPointer: " << InstructionUtils::getValueStr(srcPointer) << "\n";
#endif
            already_stripped = false;
            if(getTaintInfo(srcPointer->stripPointerCasts())) {
                srcPointer = srcPointer->stripPointerCasts();
                srcTaintInfo = getTaintInfo(srcPointer);
                already_stripped = true;
#ifdef DEBUG_LOAD_INSTR
                dbgs() << "TaintAnalysisVisitor::visitLoadInst(): Got taint info after stripping: " 
                << InstructionUtils::getValueStr(srcPointer) << "\n";
#endif
            }
        }

        //Copy the taint from tainted pointer.
        if (srcTaintInfo != nullptr) {
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "The src pointer itself is tainted.\n";
#endif
            TaintAnalysisVisitor::makeTaintInfoCopy(&I,srcTaintInfo,newTaintInfo);
        }

        if(!already_stripped) {
            if(!PointsToUtils::hasPointsToObjects(currState, this->currFuncCallSites, srcPointer)) {
#ifdef DEBUG_LOAD_INSTR
                dbgs() << "Strip srcPointer since there is no point-to info.\n";
#endif
                srcPointer = srcPointer->stripPointerCasts();
            }
        }

        // Get the src points to information.
        std::set<PointerPointsTo*>* srcPointsTo = PointsToUtils::getPointsToObjects(currState,
                                                                                    this->currFuncCallSites,
                                                                                    srcPointer);
        if (srcPointsTo != nullptr) {
            // this set stores the <fieldid, targetobject> of all the objects to which the srcPointer points to.
            std::set<std::pair<long, AliasObject *>> targetObjects;
            for (PointerPointsTo *currPointsToObj : *srcPointsTo) {
                long target_field = currPointsToObj->dstfieldId;
                AliasObject *dstObj = currPointsToObj->targetObject;
                auto to_check = std::make_pair(target_field, dstObj);
                if (std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                    targetObjects.insert(targetObjects.end(), to_check);
                    //Ok, now fetch the taint flags from the object field..
                    std::set<TaintFlag*> fieldTaintInfo, nTaintInfo;
                    dstObj->getFieldTaintInfo(target_field,fieldTaintInfo,this->makeInstLoc(&I));
                    if (fieldTaintInfo.empty()) {
#ifdef DEBUG_LOAD_INSTR
                        dbgs() << "No taint information available for: " << (const void*)dstObj << "|" << target_field << "\n";
#endif
                        continue;
                    }
                    this->makeTaintInfoCopy(&I, &fieldTaintInfo, &nTaintInfo);
                    //Now set up the load tag for the new TFs and insert them into the final "newTaintInfo".
                    for (TaintFlag *tf : nTaintInfo) {
                        if (TaintAnalysisVisitor::addNewTaintFlag(newTaintInfo,tf)) {
                            //TF inserted, set up the load tag.
                            tf->loadTag = currPointsToObj->loadTag;
                        }
                    }
                }
            }
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "Got pointee objs of srcPointer, #: " << targetObjects.size() << "\n";
#endif
        } else {
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "TaintAnalysis: Src Pointer does not point to any object.\n";
#endif
        }
        if(newTaintInfo->size()) {
            // okay. Now add the newTaintInfo
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "TaintAnalysis: Updating Taint in LoadInstruction..\n";
#endif
            updateTaintInfo(&I, newTaintInfo);
        } else {
            delete(newTaintInfo);
        }

    }

    void inferTaintMap(StoreInst &I, std::set<TaintFlag*> *srcTFs, std::set<PointerPointsTo*> *dstPtos, 
                       std::map<PointerPointsTo*,std::set<TaintFlag*>> &taintMap) {
        if (!srcTFs || !dstPtos) {
            return;
        }
#ifdef DEBUG_STORE_INSTR_MAPPING
        dbgs() << "inferTaintMap(): #srcTFs: " << srcTFs->size() << " #dstPtos: " << dstPtos->size() << "\n";
#endif
        if (srcTFs->empty() || dstPtos->size() <= 1) {
            return;
        }
        //Verify that the dst pointees share a unified loadTag.
        std::vector<TypeField*> *dtag = &((*(dstPtos->begin()))->loadTag);
        int dl = dtag->size(); 
        for (PointerPointsTo *pto : *dstPtos) {
            dl = std::min(dl,InstructionUtils::isSimilarLoadTag(dtag,&(pto->loadTag)));
            if (dl <= 0) {
#ifdef DEBUG_STORE_INSTR_MAPPING
                dbgs() << "inferTaintMap(): The load tags are not uniformed between dsts.\n";
#endif
                return;
            }
        }
        //Set up the mapping, note that here we skip the unification verification step for the src as in point-to analysis,
        //since unlike the pto records, the taint flags have multiple different sources (e.g. in a load IR they can be from both
        //the src pointer itself and the pointee mem locations..). So what we do here is more aggressive: to try best to match 
        //those TFs that can be addressed to a certain dst mem location, and only for the remaining, propagate them to all dsts.
        std::set<TaintFlag*> addedTFs;
        for (PointerPointsTo *pto : *dstPtos) {
            std::vector<TypeField*> *dt = &(pto->loadTag);
            taintMap[pto].clear();
            for (TaintFlag *tf : *srcTFs) {
                std::vector<TypeField*> *st = &(tf->loadTag);
                if (InstructionUtils::matchLoadTags(dt,st,dl,0) >= 0) {
                    taintMap[pto].insert(tf);
                    addedTFs.insert(tf);
                }else {
#ifdef DEBUG_STORE_INSTR_MAPPING
                    dbgs() << "inferTaintMap(): Skip the TF: ";
                    tf->dumpInfo_light(dbgs(),false);
                    dbgs() << " for " << pto->targetObject << "|" << pto->dstfieldId << "\n";
#endif
                }
            }
        }
        //TODO: What to do w/ the unmapped TFs..
        /*
        if (addedTFs.size() < srcTFs->size()) {
            for (TaintFlag *tf : *srcTFs) {
                if (addedTFs.find(tf) == addedTFs.end()) {
                }
            }
        }
        */
    }

    void TaintAnalysisVisitor::visitStoreInst(StoreInst &I) {
#ifdef DEBUG_STORE_INSTR
        dbgs() << "TaintAnalysisVisitor::visitStoreInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value *srcPointer = I.getValueOperand();
        std::set<TaintFlag*> *srcTaintInfo = getTaintInfo(srcPointer);
        if(srcTaintInfo == nullptr) {
            srcPointer = srcPointer->stripPointerCasts();
            srcTaintInfo = getTaintInfo(srcPointer);
        }

        //Get the mem locations to store.
        Value *dstPointer = I.getPointerOperand();
        //HZ: besides deciding whether we need to strip the pointer, the "dstTaintInfo" in the original code actually has no usage later...
        //HZ: so rewrite the original logic as below:
        //TODO: why do we need to even consider the "dstTaintInfo" when making the strip decision?
        if (!getTaintInfo(dstPointer)) {
            if (getTaintInfo(dstPointer->stripPointerCasts()) || 
                !PointsToUtils::hasPointsToObjects(currState, this->currFuncCallSites, dstPointer))
            {
                dstPointer = dstPointer->stripPointerCasts();
            }
        }
        std::set<PointerPointsTo*> *dstPointsTo = PointsToUtils::getPointsToObjects(currState, this->currFuncCallSites, dstPointer);
        std::set<PointerPointsTo*> uniqueDstPto;
        if(dstPointsTo != nullptr) {
            for (PointerPointsTo *currPointsToObj : *dstPointsTo) {
                if (std::find_if(uniqueDstPto.begin(),uniqueDstPto.end(),[currPointsToObj](const PointerPointsTo *pto){
                    return currPointsToObj->pointsToSameObject(pto);
                }) == uniqueDstPto.end())
                {
                    uniqueDstPto.insert(currPointsToObj);
                }
            }
        }
#ifdef DEBUG_STORE_INSTR
        dbgs() << "TaintAnalysisVisitor::visitStoreInst: #targetMemLoc: " << uniqueDstPto.size() << "\n";
#endif
        if (uniqueDstPto.empty()) {
            //Nowhere to taint..
            return;
        }
        bool multi_pto = (uniqueDstPto.size() > 1); 
        //Prepare either the taint flags or the taint kill, and their mapping to the taint dst.
        std::set<TaintFlag*> newTaintInfo;
        //The mapping between the taint dst and the TFs to propagate.
        std::map<PointerPointsTo*,std::set<TaintFlag*>> taintMap;
        if (srcTaintInfo && !srcTaintInfo->empty()) {
            //The src value is tainted, then we need to propagate the taint flags;
            TaintAnalysisVisitor::makeTaintInfoCopy(&I,srcTaintInfo,&newTaintInfo);
            //Try to set up the mapping between the taint flags and the taint dst if there are more than one dst.
            if (multi_pto) {
                inferTaintMap(I,&newTaintInfo,&uniqueDstPto,taintMap);
            }
        }else {
            //It's not tainted, then this is actually a taint kill if (1) there is only one target 
            //mem location (otherwise this is a weak taint kill that we will not honor to be conservative). 
            //and (2) the target mem location is tainted now (otherwise no need to kill). 
            //If so then we also need to propagate the taint kill flag.
            if (!multi_pto) {
                //Create a taint kill flag.
                TaintFlag *tf = new TaintFlag(this->makeInstLoc(&I),false,nullptr,false);
                newTaintInfo.insert(tf);
            }
        }
#ifdef DEBUG_STORE_INSTR
        dbgs() << "TaintAnalysisVisitor::visitStoreInst: #newTaintInfo: " << newTaintInfo.size() << "\n";
#endif
        if (newTaintInfo.empty()) {
            return;
        }
        //Ok now propagate the taint flags to the target mem locs, according to the mapping set up previously.
        std::set<TaintFlag*> addedTFs;
        for (PointerPointsTo *pto : uniqueDstPto) {
            std::set<TaintFlag*> *toAdd = (taintMap.find(pto) == taintMap.end() ? &newTaintInfo : &(taintMap[pto]));
            for (TaintFlag *tf : *toAdd) {
                //Don't forget the "is_weak" flag in the TF indicating whether it's a strong or weak taint.
                tf->is_weak = multi_pto;
                if (pto->targetObject->addFieldTaintFlag(pto->dstfieldId,tf)) {
                    addedTFs.insert(tf);
                }
            }
        }
        //Free the memory occupied by the unuseful TFs (e.g. duplicated in the dst mem loc).
        if (addedTFs.size() < newTaintInfo.size()) {
            for (TaintFlag *tf : newTaintInfo) {
                if (addedTFs.find(tf) == addedTFs.end()) {
                    delete(tf);
                }
            }
        }
    }

    // The following instructions are ignored.
    // we will deal with them, if we find them
    void TaintAnalysisVisitor::visitVAArgInst(VAArgInst &I) {
        // NO idea how to handle this
        assert(false);
    }

    void TaintAnalysisVisitor::visitVACopyInst(VACopyInst &I) {
        // No idea how to handle this
        assert(false);
    }

    //hz: this function tries to init the taint from user arg for functions like copy_from_user().
    void TaintAnalysisVisitor::propagateTaintToArguments(std::set<long> &taintedArgs, CallInst &I) {
        assert(taintedArgs.size() > 0);
#ifdef DEBUG_CALL_INSTR
        dbgs() << "Propagating Taint To Arguments.\n";
#endif
        for (auto currArgNo : taintedArgs) {
            Value *currArg = I.getArgOperand(currArgNo);
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Current argument: " << InstructionUtils::getValueStr(currArg) << "\n";
#endif
            std::set<PointerPointsTo*>* dstPointsTo = PointsToUtils::getPointsToObjects(currState,
                                                                                        this->currFuncCallSites,
                                                                                        currArg);
            if(dstPointsTo == nullptr) {
                currArg = currArg->stripPointerCasts();
                dstPointsTo = PointsToUtils::getPointsToObjects(currState,
                                                                this->currFuncCallSites,
                                                                currArg);
            }
            if (dstPointsTo != nullptr) {
                std::set<std::pair<long, AliasObject *>> targetObjects;
                for (PointerPointsTo *currPointsToObj : *dstPointsTo) {
                    long target_field = currPointsToObj->dstfieldId;
                    AliasObject *dstObj = currPointsToObj->targetObject;
                    if (!dstObj) {
                        continue;
                    }
                    auto to_check = std::make_pair(target_field, dstObj);
                    if (std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                        targetObjects.insert(targetObjects.end(), to_check);
                    }
                }

                bool multi_pto = (targetObjects.size() > 1);
                bool is_added = false;

                assert(targetObjects.size() > 0);
                InstLoc *currInst = this->makeInstLoc(&I);

                for(auto fieldObject : targetObjects) {
                    //Taint Tag represents the taint source, here it's the user provided data passed by functions like copy_from_user()...
                    //But we actually don't have value/type/AliasObject for this user input, so just create a dummy 
                    //Tag to stand for a certain user input.
                    TaintTag *tag = new TaintTag(0,(Type*)nullptr,false,nullptr);
                    //NOTE: "is_weak" is decided by whether there are multiple pointees.
                    TaintFlag *tf = new TaintFlag(currInst,true,tag,multi_pto);
                    // if it is pointing to first field, then taint everything
                    // else taint only corresponding field.
                    if (fieldObject.first != 0 && fieldObject.second->addFieldTaintFlag(fieldObject.first, tf)) {
#ifdef DEBUG_CALL_INSTR
                        dbgs() << "Adding Taint To field ID:"<< fieldObject.first << " of:" << fieldObject.second << ":Success\n";
#endif
                        is_added = true;
                    } else if (fieldObject.first == 0 && fieldObject.second->taintAllFields(tf)) {
#ifdef DEBUG_CALL_INSTR
                        dbgs() << "Adding Taint To All fields:"<< fieldObject.first << " of:" << fieldObject.second << ":Success\n";
#endif
                        is_added = true;
                    } else {
#ifdef DEBUG_CALL_INSTR
                        dbgs() << "Adding Arg Taint Failed.\n";
#endif
                        delete(tag);
                        delete(tf);
                    }
                }
                // if the current taint is not added to any object, free the memory.
                // delete the newTaint object.
                if(!is_added) {
                    delete(currInst);
                }

            } else {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "TaintAnalysis: Argument does not have points to information: " << InstructionUtils::getValueStr(currArg) << "\n";
#endif
            }
        }
    }

    void TaintAnalysisVisitor::setupCallContext(CallInst &I, Function *currFunction,
                                                std::vector<Instruction*> *newCallContext) {

        std::map<Value*, std::set<TaintFlag*>*> *contextTaintInfo = currState.getTaintInfo(newCallContext);

        unsigned int arg_no = 0;

        for(User::op_iterator arg_begin = I.arg_begin(), arg_end = I.arg_end(); arg_begin != arg_end; arg_begin++) {
            Value *currArgVal =(*arg_begin).get();

            if(getTaintInfo(currArgVal) || getTaintInfo(currArgVal->stripPointerCasts())) {
                unsigned int farg_no;
                farg_no = 0;
                std::set<Value*> valuesToMerge;
                // handle pointer casts
                if(!getTaintInfo(currArgVal)) {
                    currArgVal = currArgVal->stripPointerCasts();
                }
#ifdef DEBUG_CALL_INSTR
                dbgs() << "Has Taint Info:" << getTaintInfo(currArgVal)->size() << " taint flags\n";
#endif
                valuesToMerge.clear();
                valuesToMerge.insert(valuesToMerge.end(), currArgVal);

                for(Function::arg_iterator farg_begin = currFunction->arg_begin(), farg_end = currFunction->arg_end();
                    farg_begin != farg_end; farg_begin++) {
                    Value *currfArgVal = &(*farg_begin);
                    if(farg_no == arg_no) {
                        std::set<TaintFlag*> *currArgTaintInfo = mergeTaintInfo(valuesToMerge, &I);
                        // ensure that we didn't mess up.
                        //assert(currArgTaintInfo != nullptr);
                        if (currArgTaintInfo == nullptr) {
                            //This is less likely but if it happens, treat this arg as not tainted.
                            break;
                        }
#ifdef DEBUG_CALL_INSTR
                        // OK, we need to add taint info.
                        dbgs() << "Argument:" << (arg_no) << " has taint info\n";
#endif
                        (*contextTaintInfo)[currfArgVal] = currArgTaintInfo;
                        break;
                    }
                    farg_no++;
                }
            } else {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "Argument:" << (arg_no) << " does not have taint info\n";
#endif
            }
            arg_no++;
        }

    }

    void TaintAnalysisVisitor::propagateTaintToMemcpyArguments(std::vector<long> &memcpyArgs, CallInst &I) {
#ifdef DEBUG_CALL_INSTR
        dbgs() << "Processing memcpy function\n";
#endif
        // we do not need any special taint handling..because alias takes care of propagating
        // pointer, here we just need to update taint of the arguments.
        // get src operand
        Value *srcOperand = I.getArgOperand((unsigned int) memcpyArgs[0]);
        // get dst operand
        Value *dstOperand = I.getArgOperand((unsigned int) memcpyArgs[1]);

        std::set<Value*> mergeVals;
        mergeVals.insert(srcOperand);

        std::set<TaintFlag*>* newTaintInfo = this->mergeTaintInfo(mergeVals, &I);
        if(newTaintInfo != nullptr) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Trying to memcpy from tainted argument\n";
#endif
            this->updateTaintInfo(dstOperand, newTaintInfo);
        }

    }

    void TaintAnalysisVisitor::handleKernelInternalFunction(CallInst &I, Function *currFunc) {
        // see if this is a taint initiator function.
        if (TaintAnalysisVisitor::functionChecker->is_taint_initiator(currFunc)) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "This function is a taint initiator function:" << currFunc->getName() << "\n";
#endif
            // handling __copy_from_user and its friends.
            std::set<long> taintedArgs = TaintAnalysisVisitor::functionChecker->get_tainted_arguments(currFunc);
            this->propagateTaintToArguments(taintedArgs, I);
        } else if (TaintAnalysisVisitor::functionChecker->is_memcpy_function(currFunc)) {
            // Handle memcpy function..
            // get memcpy argument numbers
            std::vector<long> memcpyArgs = TaintAnalysisVisitor::functionChecker->get_memcpy_arguments(currFunc);
            //propagate taint from src to dst.
            this->propagateTaintToMemcpyArguments(memcpyArgs, I);
        } else if (TaintAnalysisVisitor::functionChecker->is_atoi_function(currFunc)) {
          // This is an atoi like function?
           // if yes? get the taint of the object pointed by the first argument.
            // propagate that to the return value.
            std::set<TaintFlag*> allPointerTaint;
            allPointerTaint.clear();
            this->getPtrTaintInfo(I.getArgOperand(0), allPointerTaint, &I);
            if(!allPointerTaint.empty()) {
                std::set<TaintFlag*> *newTaintSet = this->makeTaintInfoCopy(&I, &allPointerTaint);
                this->updateTaintInfo(&I, newTaintSet);
            }

        } else if(TaintAnalysisVisitor::functionChecker->is_sscanf_function(currFunc)) {
            // This is a sscanf function?
            // if yes? get the taint of the object pointed by the first argument.
            std::set<TaintFlag*> allPointerTaint;
            allPointerTaint.clear();
            this->getPtrTaintInfo(I.getArgOperand(0), allPointerTaint, &I);
            if(!allPointerTaint.empty()) {
                std::set<TaintFlag*> *newTaintSet = this->makeTaintInfoCopy(&I, &allPointerTaint);

                std::set<TaintFlag*> addedTaints;

                // now add taint to all objects pointed by the arguments.
                unsigned int arg_idx;
                for (arg_idx = 2; arg_idx < I.getNumArgOperands(); arg_idx++) {
                    Value *argVal = I.getArgOperand(arg_idx);
                    std::set<PointerPointsTo*> *currPtsTo = PointsToUtils::getPointsToObjects(this->currState,
                                                                                              this->currFuncCallSites,
                                                                                              argVal);
                    if(currPtsTo != nullptr) {
                        //Set "is_weak"
                        bool multi_pto = (currPtsTo->size() > 1);
                        for(auto currT : *newTaintSet) {
                            if (currT) {
                                currT->is_weak = multi_pto;
                            }
                        }
                        for(auto currP : *currPtsTo) {
                            for(auto currT : *newTaintSet) {
                                if(currP->targetObject->addFieldTaintFlag(currP->dstfieldId, currT)) {
                                    addedTaints.insert(currT);
                                }
                            }
                        }
                    }
                }
                //Free memory.
                for(auto currT:*newTaintSet) {
                    if(addedTaints.find(currT) == addedTaints.end()) {
                        delete(currT);
                    }
                }
                delete(newTaintSet);
            }

        } else {
            // TODO (below):
            // untaint all the arguments, depending on whether we are indeed calling kernel internal functions.
        }
    }

    VisitorCallback* TaintAnalysisVisitor::visitCallInst(CallInst &I, Function *currFunc,
                                                         std::vector<Instruction *> *oldFuncCallSites,
                                                         std::vector<Instruction *> *callSiteContext) {
#ifdef DEBUG_CALL_INSTR
        dbgs() << "TaintAnalysisVisitor::visitCallInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        // if this is a kernel internal function.
        if(currFunc->isDeclaration()) {
            this->handleKernelInternalFunction(I, currFunc);
            return nullptr;
        }

        // else, we need to setup taint context and create a new visitor.
        setupCallContext(I, currFunc, callSiteContext);

        // create a new TaintAnalysisVisitor
        TaintAnalysisVisitor *vis = new TaintAnalysisVisitor(currState, currFunc, callSiteContext);

        return vis;
    }

    void TaintAnalysisVisitor::stitchChildContext(CallInst &I, VisitorCallback *childCallback) {
        // just connect the taint of the return values.
        TaintAnalysisVisitor *vis = (TaintAnalysisVisitor *)childCallback;
        if(vis->retValTaints.size() > 0 ){
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Stitching return value for call instruction:";
            I.print(dbgs());
            dbgs() << "\n";
#endif
            // create new taint info.
            std::set<TaintFlag*>* newTaintInfo = new std::set<TaintFlag*>();
            for(auto currRetTaint:vis->retValTaints) {
                //NOTE: ret taint must be able to reach this call site, so no need for the taint path check.
                TaintFlag *newTaintFlag = new TaintFlag(currRetTaint, this->makeInstLoc(&I));
                newTaintInfo->insert(newTaintInfo->end(), newTaintFlag);
            }

            //update taint info
            updateTaintInfo(&I, newTaintInfo);
        }
    }

    void TaintAnalysisVisitor::visitReturnInst(ReturnInst &I) {
        // add taint of the return value to the retTaintInfo set.
        Value *targetRetVal = I.getReturnValue();
        if(targetRetVal != nullptr && (getTaintInfo(targetRetVal) || getTaintInfo(targetRetVal->stripPointerCasts()))) {
            // check if pointer casts has a role to play?
            if(!getTaintInfo(targetRetVal)){
                targetRetVal = targetRetVal->stripPointerCasts();
            }
            std::set<TaintFlag*> *currRetTaintInfo = getTaintInfo(targetRetVal);

            for(auto a : *currRetTaintInfo) {
                if(std::find_if(this->retValTaints.begin(), this->retValTaints.end(), [a](const TaintFlag *n) {
                    return  n->isTaintEquals(a);
                }) == this->retValTaints.end()) {
                    // if not insert the new taint flag into the newTaintInfo.
                    this->retValTaints.insert(this->retValTaints.end(), a);
                }
            }

        } else {
#ifdef DEBUG_RET_INSTR
            dbgs() << "Return value: " << InstructionUtils::getValueStr(&I) << ", does not have TaintFlag.\n";
#endif
        }
    }

    void TaintAnalysisVisitor::visitICmpInst(ICmpInst &I) {
        // merge taint flag of all the operands.
        std::set<Value*> allVals;
        for(unsigned i=0;i<I.getNumOperands(); i++) {
            Value* currOp = I.getOperand(i);
            allVals.insert(currOp);
        }
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }
    }

#ifdef CONTROL_TAINT
    //hz: add support for branch and switch instructions into taint analysis. 
    //TODO: In the future if we want to do control taint, we need to extend these below methods.

    //hz: the overall propagation logic of this is borrowed (w/o a plan to return) from visitCastInst.
    void TaintAnalysisVisitor::visitBranchInst(BranchInst &I) {
        //No need to handle a unconditional branch since it has no condition variable.
        if (I.isUnconditional()) {
            return;
        }
        //Get the branch condition Value.
        Value *condition = I.getCondition();
        std::set<TaintFlag*>* srcTaintInfo = getTaintInfo(condition);
        if(srcTaintInfo == nullptr) {
            condition = condition->stripPointerCasts();
            srcTaintInfo = getTaintInfo(condition);
        }
        // if there exists some taintflags..propagate them
        if(srcTaintInfo != nullptr) {
            std::set<TaintFlag*> *newTaintInfo = this->makeTaintInfoCopy(&I, srcTaintInfo);
            if(newTaintInfo != nullptr) {
                this->updateTaintInfo(&I, newTaintInfo);
            } else {
#ifdef DEBUG_BRANCH_INSTR
                dbgs() << "Taint Info cannot be propagated because the current instruction is not reachable from";
                dbgs() << "  tainted source at ";
                I.print(dbgs());
                dbgs() << "\n";
#endif
            }
        }
    }

    /*
    void TaintAnalysisVisitor::visitIndirectBrInst(IndirectBrInst &I) {
        //
    }
    */

    //hz: basically the same as visitBranchInst()
    void TaintAnalysisVisitor::visitSwitchInst(SwitchInst &I) {
        //Get the switch condition Value.
        Value *condition = I.getCondition();
        std::set<TaintFlag*>* srcTaintInfo = getTaintInfo(condition);
        if(srcTaintInfo == nullptr) {
            condition = condition->stripPointerCasts();
            srcTaintInfo = getTaintInfo(condition);
        }
        // if there exists some taintflags..propagate them
        if(srcTaintInfo != nullptr) {
            std::set<TaintFlag*> *newTaintInfo = this->makeTaintInfoCopy(&I, srcTaintInfo);
            if(newTaintInfo != nullptr) {
                this->updateTaintInfo(&I, newTaintInfo);
            } else {
#ifdef DEBUG_BRANCH_INSTR
                dbgs() << "Taint Info cannot be propagated because the current instruction is not reachable from";
                dbgs() << "  tainted source at ";
                I.print(dbgs());
                dbgs() << "\n";
#endif
            }
        }
    }
#endif

}
