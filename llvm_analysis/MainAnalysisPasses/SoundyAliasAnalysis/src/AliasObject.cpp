#include "AliasObject.h"

using namespace llvm;

namespace DRCHECKER {

    std::map<Type*,std::map<Function*,std::set<OutsideObject*>>> sharedObjCache;

    Function *currEntryFunc = nullptr;

    bool validTyForOutsideObj(Type *ty) {
        if (!ty || !dyn_cast<CompositeType>(ty)) {
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
            dbgs() << "validTyForOutsideObj(): it's not a composite type, cannot create the outside obj!\n";
#endif
            return false;
        }
        if (InstructionUtils::isNullCompTy(ty)) {
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
            dbgs() << "validTyForOutsideObj(): it's an opaque struct type or null composite type, cannot create the outside obj!\n";
#endif
            return false;
        }
        return true;
    }

    void AliasObject::logFieldAccess(long srcfieldId, Instruction *targetInstr, const std::string &msg) {
        dbgs() << "\n*********FieldAccess(" << msg << ")**********\n";
        dbgs() << "Current Inst: " << InstructionUtils::getValueStr(targetInstr) << "\n";
        dbgs() << InstructionUtils::getTypeStr(this->targetType) << " | " << srcfieldId << " OBJ: " << (const void*)this << "\n";
        dbgs() << "Object Ptr: " << InstructionUtils::getValueStr(this->getValue()) << "\n";
        if (this->getValue()){
            /*
               if(dyn_cast<Instruction>(this->targetVar)){
                    dbgs() << "\n";
                    dyn_cast<Instruction>(this->targetVar)->getFunction()->print(dbgs());
               }
             */
        }
        dbgs() << "*******************\n";
    }

    //Taint the point-to object by field "srcfieldId" according to the field taint info.
    void AliasObject::taintSubObj(AliasObject *newObj, long srcfieldId, InstLoc *targetInstr) {
        std::set<TaintFlag*> *fieldTaint = this->getFieldTaintInfo(srcfieldId);
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        dbgs() << "AliasObject::taintSubObj(): Trying to get taint for field:" << srcfieldId << " of host object: " << (const void*)this << "\n";
#endif
        if(fieldTaint != nullptr) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::taintSubObj(): Adding taint of field:" << srcfieldId << " to sub object: " << (const void*)newObj << "\n";
#endif
            for(auto existingTaint:*fieldTaint) {
                TaintFlag *newTaint = new TaintFlag(existingTaint,targetInstr);
                newObj->taintAllFieldsWithTag(newTaint);
            }
            newObj->is_taint_src = true;
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "##Set |is_taint_src| to true.\n";
#endif
        } else {
            // if all the contents are tainted?
            if(this->all_contents_tainted) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "AliasObject::taintSubObj(): Trying to get field from an object whose contents are fully tainted\n";
#endif
                assert(this->all_contents_taint_flag != nullptr);
                TaintFlag *newTaint = new TaintFlag(this->all_contents_taint_flag,targetInstr);
                newObj->taintAllFieldsWithTag(newTaint);
                newObj->is_taint_src = true;
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "##Set |is_taint_src| to true.\n";
#endif
            }
        }
    }

    Type *getLoadedPointeeTy(Instruction *targetInstr) {
        if (targetInstr && dyn_cast<LoadInst>(targetInstr)) {
            Type *ptrTy = targetInstr->getType();
            if (ptrTy->isPointerTy()) {
                return ptrTy->getPointerElementType();
            }
        }
        return nullptr;
    }

    //We have switched to a different level 0 entry function, need to reset the activation status of the ptos.
    void AliasObject::resetPtos(long fid, Instruction *entry) {
#ifdef DEBUG_UPDATE_FIELD_POINT
        dbgs() << "AliasObject::resetPtos(): Reset field pto for: " << (const void*)this << " | " << fid;
        dbgs() << ", switch entry to: ";
        InstructionUtils::printInst(entry,dbgs());
#endif
        if (this->pointsTo.find(fid) == this->pointsTo.end()) {
            return;
        }
        std::set<ObjectPointsTo*> *srcPto = &(this->pointsTo[fid]);
        for (ObjectPointsTo *pto : *srcPto) {
            if (pto && pto->propogatingInst) {
                InstLoc *pil = pto->propogatingInst;
                if (pto->is_active && pil->hasCtx() && (*pil->ctx)[0] != entry) {
                    //Deactivate it.
                    this->activateFieldPto(pto,false);
#ifdef DEBUG_UPDATE_FIELD_POINT
                    dbgs() << "AliasObject::resetPtos(): de-activate point-to: ";
                    pto->print(dbgs());
#endif
                }
                if (!pto->is_active && !pil->hasCtx()) {
                    //This is a deactivated global preset pto, need to re-activate it since we're on a new entry.
                    this->activateFieldPto(pto,true);
#ifdef DEBUG_UPDATE_FIELD_POINT
                    dbgs() << "AliasObject::resetPtos(): re-activate point-to: ";
                    pto->print(dbgs());
#endif
                }
            }
        }
    }

    void AliasObject::getLivePtos(long fid, InstLoc *loc, std::set<ObjectPointsTo*> *retPto) {
        if (this->pointsTo.find(fid) == this->pointsTo.end()) {
            return;
        }
        std::set<ObjectPointsTo*> *srcPto = &(this->pointsTo[fid]);
        if (!srcPto || !retPto || !loc) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::getLivePtos(): !srcPto || !retPto || !loc\n";
#endif
            return;
        }
        //Reactivation check: if there has been a level 0 entry function change (e.g. we have finished analyzing ioctl_0 and started
        //ioctl_1) since last update to the field pto set, we then need to:
        //(1) deactivate those active pto records set up when analyzing the previous entry functions.
        //(2) re-activate those inactive preset pto records (e.g. global struct definition) killed by last entry function.
        //The criteria: when there exists any active pto record whose update site belongs to a different level 0 entry than "loc".
        if (loc->hasCtx() && (*loc->ctx)[0]) {
            for (ObjectPointsTo *pto : *srcPto) {
                if (pto && pto->is_active && pto->propogatingInst) {
                    InstLoc *pil = pto->propogatingInst;
                    if (pil->hasCtx() && (*pil->ctx)[0] && (*loc->ctx)[0] != (*pil->ctx)[0]) {
                        //Do the reactivation..
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                        dbgs() << "AliasObject::getLivePtos(): Reset the field pto due to level 0 entry switch!\n";
#endif
                        this->resetPtos(fid,(*loc->ctx)[0]);
                        break;
                    }
                }
            }
        }
        int stCnt = retPto->size();
        //Preliminary processing: filter out the inactive pto records.
        std::set<ObjectPointsTo*> actPtos;
        for (ObjectPointsTo *pto : *srcPto) {
            if (pto && pto->is_active) {
                actPtos.insert(pto);
            }
        }
        if (actPtos.empty()) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::getLivePtos(): No active/valid pto records after pre-filtering!\n";
#endif
            return;
        }
        //Step 1: reachability test - whether a src pto (updated at a certain InstLoc) can reach current location.
        //NOTE: here we need to consider the case where one pto is killed along its path to the destination by another strong pto update.
        std::set<InstLoc*> blocklist;
        for (ObjectPointsTo *pto : actPtos) {
            if (pto->propogatingInst && !pto->is_weak) {
                blocklist.insert(pto->propogatingInst);
            }
        }
        for (ObjectPointsTo *pto : actPtos) {
            if (pto->propogatingInst) {
                if (loc->reachable(pto->propogatingInst,&blocklist)) {
                    retPto->insert(pto);
                }
            }else {
                //TODO: is it correct to conservatively add the pto records w/o update sites to the live pto set?
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "!!! AliasObject::getLivePtos(): pto w/o update site info: ";
                pto->print(dbgs());
#endif
                retPto->insert(pto);
            }
        }
        //Step 2: post-dom test - some pto records may "kill" others due to post-dom relationship.
        //TODO: do we really need this test here given that we have already done such a test when updating the field pto.
        //Step 3: de-duplication test. 
        //TODO: we may not need to do this as well since it's performed at the update time.
        //
        //The final step: path coverage check.
        //Can these pto records in "retPto" cover every path from the very beginning to current "loc"?
        //If not we need to create dummy objs for the uncovered paths.
        //If no live ptos then the caller will create dummy obj itself, no need for us. 
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        dbgs() << "AliasObject::getLivePtos(): There are currently " << retPto->size() << " live ptos in the return set, before path coverage test.\n";
#endif
        if (retPto->size() > 0) {
            bool has_global_pto= false;
            for (ObjectPointsTo *pto : *srcPto) {
                if (!pto->propogatingInst) {
                    continue;
                }
                InstLoc *pil = pto->propogatingInst;
                if (!pil->hasCtx()) {
                    has_global_pto = true;
                    break;
                }
                if (pil->hasCtx() && pil->ctx->size() == 1 && loc->hasCtx() && 
                    (*loc->ctx)[0] == (*pil->ctx)[0] && pil->inst && pil->inst == (*pil->ctx)[0]) {
                    //Has a pto set up at the level 0 function entry.
                    has_global_pto = true;
                    break;
                }
            }
            //Already have global pto (can follow any path) -> It's either activated now, or deactivated because it's completely blocked -> no need to test the path coverage any more.
            if (!has_global_pto) {
                //Test whether current active ptos can cover all paths from entry to "loc".
                blocklist.clear();
                for (ObjectPointsTo *pto : *retPto) {
                    if (pto && pto->propogatingInst) {
                        blocklist.insert(pto->propogatingInst);
                    }
                }
                if (loc->chainable(0,&blocklist,true)) {
                    //Ok, need to create the "default" dummy obj at the entry...
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                    dbgs() << "AliasObject::getLivePtos(): The current live ptos cannot cover every path to the current use site, needs to create dummy pto at the entry...\n";
#endif
                    if (loc->hasCtx() && (*loc->ctx)[0]) {
                        std::vector<Instruction*> *newCtx = new std::vector<Instruction*>(loc->ctx->begin(),loc->ctx->begin()+1);
                        InstLoc *il = new InstLoc((*loc->ctx)[0],newCtx);
                        std::set<std::pair<long, AliasObject*>> newObjs;
                        this->createFieldPointee(fid, newObjs, loc, il);
                        if (newObjs.empty()) {
                            //This is strange...
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                            dbgs() << "AliasObject::getLivePtos(): Fail to create dummy pto...\n";
#endif
                            return;
                        }
                        //We need to add these newly created pto (which are also live now) to the return set.
                        int cnt = 0;
                        for (ObjectPointsTo *pto : *srcPto) {
                            if (pto && pto->propogatingInst == il && pto->is_active) {
                                retPto->insert(pto);
                                ++cnt;
                            }
                        }
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                        dbgs() << "AliasObject::getLivePtos(): " << cnt << " dummy ptos (at the entry) inserted!\n";
#endif
                    }
                }
            }else {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "AliasObject::getLivePtos(): The field already has global pto, so no path coverage test...\n";
#endif
            }
        }
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        dbgs() << "AliasObject::getLivePtos(): ";
        this->logFieldPto(fid,dbgs());
        dbgs() << "AliasObject::getLivePtos(): #final_ret: " << retPto->size() - stCnt << "\n";
#endif
        return;
    }

    //An improved version of "fetchPointsToObjects", we need to consider the type of each field.
    void AliasObject::fetchPointsToObjects(long srcfieldId, std::set<std::pair<long, AliasObject*>> &dstObjects, InstLoc *currInst) {
        /***
         * Get all objects pointed by field identified by srcfieldID
         *
         * i.e if a field does not point to any object.
         * Automatically generate an object and link it with srcFieldId
         */
        Instruction *targetInstr = currInst ? dyn_cast<Instruction>(currInst->inst) : nullptr;
        //What's the expected type of the fetched point-to object?
        //TODO: deal with other types of insts that can invoke "fetchPointsToObjects" in its handler.
        Type *expObjTy = getLoadedPointeeTy(targetInstr);
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        logFieldAccess(srcfieldId, targetInstr, "FETCH");
#endif
        //Collapse the array/vector into a single element.
        //TODO: index-sensitive array access.
        if (this->targetType && dyn_cast<SequentialType>(this->targetType)) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::fetchPointsToObjects: the host is an array/vector, now set srcfieldId to 0.\n";
#endif
            srcfieldId = 0;
        }
        AliasObject *host = this->getNestedObj(srcfieldId);
        if (!host) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::fetchPointsToObjects: failed to obtain the innermost nested field!\n";
#endif
            return;
        }
        if (host != this) {
            //This means what we need to fetch is in an embedded field obj at the original "srcfieldId", so the new field should be 0 in the emb obj.
            srcfieldId = 0;
        }
        //Fetch the pto from the specified field...
        bool hasObjects = false;
        if (host->pointsTo.find(srcfieldId) != host->pointsTo.end()) {
            //Decide which pto records are valid at current load site (i.e. the InstLoc "currInst").
            std::set<ObjectPointsTo*> livePtos;
            host->getLivePtos(srcfieldId,currInst,&livePtos);
            for (ObjectPointsTo *obj : livePtos) {
                if (obj->fieldId == srcfieldId && obj->targetObject) {
                    //We handle a special case here:
                    //Many malloc'ed HeapLocation object can be of the type i8*, while only in the later code the pointer will be converted to a certain struct*,
                    //we choose to do this conversion here, specifically we need to:
                    //(1) change the object type to the "expObjTy",
                    //(2) setup the taint information properly.
#ifdef DEBUG_CHANGE_HEAPLOCATIONTYPE
                    //dbgs() << "AliasObject::fetchPointsToObjects: isHeapLocation: " << (obj->targetObject && obj->targetObject->isHeapLocation()) << " dstField: " << obj->dstfieldId;
                    //dbgs() << " expObjTy: " << InstructionUtils::getTypeStr(expObjTy) << "\n";
#endif
                    if (obj->dstfieldId == 0 && obj->targetObject->isHeapLocation() && 
                        expObjTy && dyn_cast<CompositeType>(expObjTy) && obj->targetObject->targetType != expObjTy) 
                    {
#ifdef DEBUG_CHANGE_HEAPLOCATIONTYPE
                        dbgs() << "AliasObject::fetchPointsToObjects: isHeapLocation: " << (obj->targetObject && obj->targetObject->isHeapLocation()) << " dstField: " << obj->dstfieldId;
                        dbgs() << " expObjTy: " << InstructionUtils::getTypeStr(expObjTy) << "\n";
                        dbgs() << "AliasObject::fetchPointsToObjects: Change type of the HeapLocation.\n";
#endif
                        //Change type.
                        obj->targetObject->reset(targetInstr,expObjTy);
                        //Do the taint accordingly.
                        host->taintSubObj(obj->targetObject,srcfieldId,currInst);
                    }
                    //Anyway here we're sure that we have the point-to record and we don't need to create dummy pointees any more,
                    //although the recorded pointee may have already been included in the "dstObjects" (e.g. load src pointer can have
                    //other target objects whose pointee set has already included this recorded pointee).
                    hasObjects = true;
                    auto p = std::make_pair(obj->dstfieldId, obj->targetObject);
                    if (std::find(dstObjects.begin(), dstObjects.end(), p) == dstObjects.end()) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                        dbgs() << "Found a new obj in |pointsTo| records, insert it to the dstObjects.\n";
                        dbgs() << "Type: " << InstructionUtils::getTypeStr(obj->targetObject->targetType) << " | " << obj->dstfieldId << " | is_taint_src:" << obj->targetObject->is_taint_src << "\n";
                        dbgs() << "Val: " << InstructionUtils::getValueStr(obj->targetObject->getValue()) << " ID: " << (const void*)(obj->targetObject) << "\n";
#endif
                        dstObjects.insert(dstObjects.end(), p);
                    }
                }
            }
        }
        if (hasObjects || InstructionUtils::isAsanInst(targetInstr)) {
            return;
        }
        //Try to create a dummy object.
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        dbgs() << "AliasObject::fetchPointsToObjects: No existing pto records for the field, try to create a dummy obj.\n";
#endif
        //since we cannot find any existing pto records, we need to create a "default" pto for current field who should exist at current level 0 function entry,
        //thus, we need to set the "siteInst" to the entry, instead of the "currInst".
        if (currInst && currInst->hasCtx() && (*currInst->ctx)[0]) {
            std::vector<Instruction*> *newCtx = new std::vector<Instruction*>(currInst->ctx->begin(),currInst->ctx->begin()+1);
            InstLoc *il = new InstLoc((*currInst->ctx)[0],newCtx);
            host->createFieldPointee(srcfieldId, dstObjects, currInst, il);
        }else {
            dbgs() << "!!! AliasObject::fetchPointsToObjects: currInst does not have a valid level 0 entry function!\n";
            host->createFieldPointee(srcfieldId, dstObjects, currInst);
        }
    }

    //Create a dummy field pto object.
    //"currInst" is the instruction where we actually need to use the field pto (but find it's not present), while "siteInst" is the location
    //we need to address the newly created field pto to (i.e. its "propagatingInst"). E.g.
    //func_entry: //site 0... if (..) {//site 1} else {//site 2}
    //Imagine "currInst" is in site 1, and site 2 also needs to use the same field pto, if in site 1 we don't have any pto records,
    //that means the pto is absent from the very beginning (e.g. function entry), so we actually need to create the pto in site 0 (i.e. siteInst)
    //so that site 2 later can also use it.
    void AliasObject::createFieldPointee(long fid, std::set<std::pair<long, AliasObject*>> &dstObjects, InstLoc *currInst, InstLoc *siteInst) {
        if (siteInst == nullptr) {
            siteInst = currInst;
        }
        Instruction *targetInstr = currInst ? dyn_cast<Instruction>(currInst->inst) : nullptr;
        //What's the expected type of the fetched point-to object?
        //TODO: deal with other types of insts that can invoke "fetchPointsToObjects" in its handler.
        Type *expObjTy = getLoadedPointeeTy(targetInstr);
        //Get the type of the field for which we want to get the pointee.
        AliasObject *hostObj = this->getNestedObj(fid);
        if (!hostObj) {
            return;
        }
        //It's possible that the embedded object already has the point-to record for field 0, if so, we just return the existing pto records.
        //If not, the "fetchPointsToObjects" will again invoke "createFieldPointee" to create the dummy object.
        if (hostObj != this) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::createFieldPointee(): fetch the point-to from the embedded composite field.\n"; 
#endif
            return hostObj->fetchPointsToObjects(fid,dstObjects,currInst);
        }
        Type *ety = this->getFieldTy(fid);
        //Decide the type of the dummy object we want to create..
        //NOTE: a non-pointer field can also be converted to a pointer and thus have pointees... 
        Type *real_ty = nullptr;
        if (ety->isPointerTy() && !InstructionUtils::isPrimitivePtr(ety) && !InstructionUtils::isNullCompPtr(ety)) {
            real_ty = ety->getPointerElementType();
        }else if (expObjTy && !InstructionUtils::isPrimitiveTy(expObjTy)) {
            //NOTE: we handle a special case here, sometimes the field type in the struct can be "void*" or "char*" ("i8*"), but it can be converted to "struct*" in the load,
            //if this is the case, we will create the dummy object based on the real converted type and still make this "void*/char*" field point to the new obj. 
            real_ty = expObjTy;
        }
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        dbgs() << "AliasObject::createFieldPointee(): about to create dummy obj of type: " << InstructionUtils::getTypeStr(real_ty) << "\n"; 
#endif
        if (!real_ty) {
            return;
        }
        //Create the dummy obj according to the dst type.
        if (real_ty->isFunctionTy()) {
            //This is a function pointer w/o point-to function, which can cause trobule later in resolving indirect function call.
            //We can try to do some smart resolving here by looking at the same-typed global constant objects.
#ifdef SMART_FUNC_PTR_RESOLVE
            std::vector<Function*> candidateFuncs;
            hostObj->getPossibleMemberFunctions(targetInstr, dyn_cast<FunctionType>(real_ty), hostObj->targetType, fid, candidateFuncs);
            for (Function *func : candidateFuncs) {
                GlobalObject *newObj = new GlobalObject(func);
                //Update points-to
                hostObj->addObjectToFieldPointsTo(fid,newObj,siteInst,false);
                dstObjects.insert(dstObjects.end(), std::make_pair(0, newObj));
            }
#endif
        }else if (validTyForOutsideObj(real_ty)) {
            OutsideObject *newObj = new OutsideObject(targetInstr,real_ty);
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::createFieldPointee(): New obj created. Id: " << (const void*)newObj << "\n";
#endif
            newObj->auto_generated = true;
            // get the taint for the field and add that taint to the newly created object
            hostObj->taintSubObj(newObj,fid,siteInst);
            //Handle some special cases like mutual point-to in linked list node "list_head".
            hostObj->handleSpecialFieldPointTo(newObj,fid,siteInst);
            //Update points-to
            hostObj->addObjectToFieldPointsTo(fid,newObj,siteInst,false);
            dstObjects.insert(dstObjects.end(), std::make_pair(0, newObj));
        }else {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "fetchPointsToObjects(): the pointee type is invalid to create a dummy obj!\n";
#endif
        }
    }

    //The "fid" may be a composite field, if this is the case, we recursively get the inner most AliasObject whose field 0 is no more composite,
    //otherwise, just return "this" (i.e. its "fid" field is not composite by itself).
    AliasObject *AliasObject::getNestedObj(long fid) {
        //Get the innermost non-somposite field.
        //There will be several cases here:
        //(1) The dst field is not composite, then we can return directly;
        //(2) The dst field is an embedded composite, we need to recursively extract the first field of it until we get a non-composite field;
        //(3) No type information for the dst element is available, return directly.
        AliasObject *hostObj = this;
        while (true) {
            int err = 0;
            Type *ety = hostObj->getFieldTy(fid,&err);
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::getNestedObj(): " << (const void*)hostObj << " | " << fid << " : " << InstructionUtils::getTypeStr(ety) << "\n";
#endif
            if (!ety) {
                if (err == 2) {
                    //The requested field id is OOB, sth bad has happended.
                    dbgs() << "\n!!! AliasObject::getNestedObj(): field ID OOB!";
                    dbgs() << " Below is the info about current AliasObject...\n";
                    logFieldAccess(fid, nullptr, "ERROR");
                }
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "\nAliasObject::getNestedObj(): Cannot decide the type of the dst element!\n";
#endif
                return nullptr;
            }
            if (!dyn_cast<CompositeType>(ety)) {
                return hostObj;
            }
            //NOTE: this is actually getOrCreateEmbObj()
            AliasObject *newObj = DRCHECKER::createEmbObj(hostObj, fid);
            if (!newObj) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "\n!!! AliasObject::getNestedObj(): Failed to create the emb obj.\n"; 
#endif
                return nullptr;
            }
            //assert(InstructionUtils::same_types(newObj->targetType,ety));
            hostObj = newObj;
            fid = 0;
        }
        return nullptr;
    }

    void AliasObject::updateFieldPointsTo(long srcfieldId, std::set<PointerPointsTo*>* dstPointsTo, InstLoc *propogatingInstr, int is_weak) {
        /***
         * Add all objects in the provided pointsTo set to be pointed by the provided srcFieldID
         */
#ifdef DEBUG_UPDATE_FIELD_POINT
        dbgs() << "updateFieldPointsTo() for: " << InstructionUtils::getTypeStr(this->targetType) << " | " << srcfieldId;
        dbgs() << " Host Obj ID: " << (const void*)this << "\n";
#endif
        if (!dstPointsTo || !dstPointsTo->size()) {
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "updateFieldPointsTo(): Null dstPointsTo.\n";
#endif
            return;
        }
        AliasObject *host = this;
        if (host->targetType) {
            //Array collapse
            if (dyn_cast<SequentialType>(host->targetType)) {
#ifdef DEBUG_UPDATE_FIELD_POINT
                dbgs() << "updateFieldPointsTo(): sequential host, set srcfieldId to 0.\n";
#endif
                srcfieldId = 0;
            }
            //If the "srcfieldId" is an embedded struct/array, we need to recursively update the fieldPointsTo in the embedded object instead of current host object.
            host = host->getNestedObj(srcfieldId);
            if (!host) {
                //TODO: return or go ahead w/ "this"?
#ifdef DEBUG_UPDATE_FIELD_POINT
                dbgs() << "!!! updateFieldPointsTo(): Failed to get the nested field!\n";
#endif
                return;
            }
            if (host != this) {
                //This means what we need to update is an embedded obj at the original "srcfieldId", so the new field should be 0 in the emb obj.
                srcfieldId = 0;
            }
        }else {
            //Is this possible?
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "!!! updateFieldPointsTo(): null type info for this host obj!\n";
#endif
        }
        host->updateFieldPointsTo_do(srcfieldId,dstPointsTo,propogatingInstr,is_weak);
    }

    //Do the real job of field pto update.
    void AliasObject::updateFieldPointsTo_do(long srcfieldId, std::set<PointerPointsTo*> *dstPointsTo, InstLoc *propogatingInstr, int is_weak) {
        if (!dstPointsTo || !dstPointsTo->size()) {
            return;
        }
        //preprocessing: deduplication and unify "fieldId" and "propInst".
        std::set<ObjectPointsTo*> unique_pto;
        for (PointerPointsTo *pto : *dstPointsTo) {
            if (!pto) {
                continue;
            }
            bool unique = true;
            for (ObjectPointsTo *t : unique_pto) {
                //NOTE: pto in "dstPointsTo" should all share the same "propogatingInstr", so we only need to care about their dst obj and field here.
                if (!t->pointsToSameObject(pto)) {
                    //Obviously different.
                    continue;
                }
                //if both pointed object and field are same and only "is_weak" is different, then just make "is_weak = false" (i.e. strong update)
                //for the existing pto record. 
                if (t->is_weak != pto->is_weak) {
                    t->is_weak = false;
                }
                //exclude this "pto" since it's duplicated
                unique = false;
                break;
            }
            if (unique) {
                ObjectPointsTo *npto = pto->makeCopy();
                //Before inserting the pto to the unique set, force set its "fieldId" and "propInst" to be correct.
                npto->fieldId = srcfieldId;
                npto->propogatingInst = propogatingInstr;
                //Insert
                unique_pto.insert(npto);
            }
        }
        if (!unique_pto.size()) {
            return;
        }
        //honor the "is_weak" arg here.
        if (is_weak >= 0) {
            for (ObjectPointsTo *pto : unique_pto) {
                pto->is_weak = !!is_weak;
            }
        }
        //Ok, now try to insert records in "unique_pto" to field points-to.
        //to_add: the pto records we should insert in the end (e.g. we may have duplicated records in existing field pto).
        //to_del: The existing pto records we should remove (e.g. overridden by new pto due to CFG relationship like post-dominator).
        //NOTE that instead of actually removing the overridden pto, we will mark it as "inactive" so the later load won't consider
        //it. The reason is that in the bug detection phase, we need to have a record of all ever existed pto relationship.
        std::set<ObjectPointsTo*> to_add, to_del;
        for (ObjectPointsTo *pto : unique_pto) {
            //Kill every existing pto we can, then decide whether we need to add current new pto.
            bool is_dup = false;
            for (ObjectPointsTo *e : this->pointsTo[srcfieldId]) {
                //The kill criteria: current pto is a strong update and it post-dominates an existing pto.
                //NOTE that we only need to kill those active pto records, since inactive ones are already killed.
                if (e->is_active && !pto->is_weak) {
                    //Ok, it's a strong update, decide whether it post-dominates "e", if so, delete "e" from existing pto set.
                    if (pto->propogatingInst && pto->propogatingInst->postDom(e->propogatingInst)) {
                        to_del.insert(e);
                        continue;
                    }
                }
                //Is "e" identical to "pto"?
                //No need to compare if we already decided it's duplicated.
                if (is_dup) {
                    continue;
                }
                //(1) Basic pto inf should be the same.
                if (!e->isIdenticalPointsTo(pto)) {
                    continue;
                }
                //(2) Update site should be the same.
                if (!e->propogatingInst != !pto->propogatingInst) {
                    continue;
                }
                if (e->propogatingInst && !e->propogatingInst->same(pto->propogatingInst)) {
                    continue;
                }
                //Ok, we can already say they are identical pto records and no need to insert "pto".
                is_dup = true;
                //But if their "is_weak" are different, we will set the existing pto to a strong update anyway.
                if (e->is_weak != pto->is_weak) {
                    e->is_weak = false;
                }
                //Re-activate the existing pto due to the fact that a duplicated one is freshly inserted.
                this->activateFieldPto(e,true);
            }
            if (!is_dup) {
                to_add.insert(pto);
            }else {
                //Note that each pto record in "unique_pto" is our newly created copy in this func, so we need to free the memory.
                delete(pto);
            }
        }
        //Do the actual deletion(de-activation) and insertion(activation).
        for (ObjectPointsTo *x : to_del) {
            this->activateFieldPto(x,false);
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "updateFieldPointsTo_do(): de-activate point-to: ";
            x->print(dbgs());
#endif
            /*
            this->pointsTo[srcfieldId].erase(x);
            //Don't forget to update the "pointsFrom" records of the affected objects.
            if (x->targetObject) {
                x->targetObject->erasePointsFrom(this,x);
            }
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "updateFieldPointsTo_do(): del point-to: ";
            x->print(dbgs());
#endif
            delete(x);
            */
        }
        for (ObjectPointsTo *x : to_add) {
            this->pointsTo[srcfieldId].insert(x);
            //Don't forget to update the "pointsFrom" records of the affected objects.
            if (x->targetObject) {
                x->targetObject->addPointsFrom(this,x);
            }
            this->activateFieldPto(x,true);
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "updateFieldPointsTo_do(): add and activate point-to: ";
            x->print(dbgs());
#endif
        }
#ifdef DEBUG_UPDATE_FIELD_POINT
        dbgs() << "updateFieldPointsTo_do(): After updates: "; 
        this->logFieldPto(srcfieldId,dbgs());
#endif
    }

    void ObjectPointsTo::print(llvm::raw_ostream& OS) {
        if (this->targetObject) {
            OS << this->fieldId << " -> " << InstructionUtils::getTypeStr(this->targetObject->targetType) << " | " << this->dstfieldId;
            OS << " Tgt Obj ID: " << (const void*)(this->targetObject) << "\n";
        }
    }

    OutsideObject* createOutsideObj(Type *ty, bool taint, std::set<TaintFlag*> *existingTaints) {
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
        dbgs() << "Type-based createOutsideObj(): " << InstructionUtils::getTypeStr(ty) << "\n";
#endif
        if (!validTyForOutsideObj(ty)) {
            return nullptr;
        }
        OutsideObject *newObj = new OutsideObject(nullptr, ty);
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
        dbgs() << "Type-based createOutsideObj(): New obj created: " << (const void*)newObj << "\n";
#endif
        //All outside objects are generated automatically.
        newObj->auto_generated = true;
        //Need taint?
        if (taint) {
            if (existingTaints && !existingTaints->empty()) {
                for (TaintFlag *currTaint : *existingTaints) {
                    newObj->taintAllFieldsWithTag(currTaint);
                }
                newObj->is_taint_src = true;
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
                dbgs() << "Type-based createOutsideObj(): set |is_taint_src| for the outside obj.\n";
#endif
            }else {
                //We don't have a value/pointer here to generate a TaintFlag...
                //TODO:
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
                dbgs() << "!!!Type-based createOutsideObj(): trying to taint w/o existingTaints...\n";
#endif
            }
        }
        return newObj;
    }

    //NOTE: this function is used to setup the pto record of a Value to its newly created dummy object, so there must be no existing pto
    //records for this value before, otherwise we don't need to create dummy obj for it.
    int updatePointsToRecord(InstLoc *vloc, std::map<Value*,std::set<PointerPointsTo*>*> *currPointsTo, AliasObject *newObj, long fid, long dfid) {
        Value *p = nullptr;
        if (vloc) {
            p = vloc->inst;
        }
        if (!newObj || !p) {
            return 0;
        }
        //NOTE: default is_Weak setting (i.e. strong update) is ok for top-level vars.
        PointerPointsTo *newPointsTo = new PointerPointsTo(p,fid,newObj,dfid,vloc,false);
        newObj->pointersPointsTo.insert(newObj->pointersPointsTo.end(),newPointsTo);
        //Set up point-to records in the global state.
        if (currPointsTo) {
            std::set<PointerPointsTo *> *newPointsToSet = new std::set<PointerPointsTo *>();
            newPointsToSet->insert(newPointsToSet->end(), newPointsTo);
            (*currPointsTo)[p] = newPointsToSet;
            return 1;
        }
        return 0;
    }

    OutsideObject* createOutsideObj(InstLoc *vloc, std::map<Value*,std::set<PointerPointsTo*>*> *currPointsTo, bool taint, std::set<TaintFlag*> *existingTaints) {
        Value *p = nullptr;
        if (vloc) {
            p = vloc->inst;
        }
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
        dbgs() << "createOutsideObj(): ";
        if(p){
            dbgs() << InstructionUtils::getValueStr(p) << "  |  " << p->getName().str() + " : " << InstructionUtils::getTypeStr(p->getType());
        }
        dbgs() << "\n";
#endif
        //First do some sanity checks, we need to make sure that "p" is a pointer of a composite type.
        if (!(p && p->getType()->isPointerTy() && validTyForOutsideObj(p->getType()->getPointerElementType()))) {
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
            dbgs() << "createOutsideObj(): It's not a pointer to the composite type! Cannot create an outside object!\n";
#endif
            return nullptr;
        }
        //Don't create OutsideObject for null ptr.
        if (p->getName().str().empty() && !dyn_cast<Instruction>(p)){
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
            dbgs() << "createOutsideObj(): Null value name! Cannot create an outside object!\n";
#endif
            return nullptr;
        }
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
        dbgs() << "createOutsideObj(): Try to create new outside object.\n";
#endif
        //Create a new outside object.
        //OutsideObject *newObj = new OutsideObject(p, p->getType()->getContainedType(0));
        OutsideObject *newObj = new OutsideObject(p, p->getType()->getPointerElementType());
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
        dbgs() << "createOutsideObj(): New obj created: " << (const void*)newObj << "\n";
#endif
        //All outside objects are generated automatically.
        newObj->auto_generated = true;
        //Set up point-to records inside the AliasObject.
        updatePointsToRecord(vloc,currPointsTo,newObj);
        //Need taint?
        if (taint) {
            if (existingTaints && !existingTaints->empty()) {
                for (TaintFlag *currTaint : *existingTaints) {
                    newObj->taintAllFieldsWithTag(currTaint);
                }
            }else {
                //The original pointer is not tainted, treat it as a global state.
                TaintFlag *currFlag = new TaintFlag(vloc, true);
                newObj->taintAllFieldsWithTag(currFlag);
            }
            newObj->is_taint_src = true;
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
            dbgs() << "createOutsideObj(): set |is_taint_src| for the outside obj.\n";
#endif
        }
        return newObj;
    }

    AliasObject *createEmbObj(AliasObject *hostObj, long host_dstFieldId, InstLoc *vloc, std::map<Value*, std::set<PointerPointsTo*>*> *currPointsTo) {
#ifdef DEBUG_CREATE_EMB_OBJ
        dbgs() << "Start createEmbObj()\n";
#endif
        Value *v = vloc ? vloc->inst : nullptr;
        AliasObject *newObj = nullptr;
        if (!hostObj || !hostObj->targetType) {
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "createEmbObj(): (!hostObj || !hostObj->targetType)\n";
#endif
            return nullptr;
        }
#ifdef DEBUG_CREATE_EMB_OBJ
        dbgs() << "createEmbObj(): host type: " << InstructionUtils::getTypeStr(hostObj->targetType) << " | " << host_dstFieldId << " ID: " << (const void*)(hostObj) << "\n";
#endif
        if (dyn_cast<SequentialType>(hostObj->targetType)) {
            //We collapse the array/vector to a single element.
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "createEmbObj(): host is an array/vector, set host_dstFieldId to 0.\n";
#endif
            host_dstFieldId = 0;
        }
        Type *ety = nullptr;
        if (dyn_cast<CompositeType>(hostObj->targetType) && InstructionUtils::isIndexValid(hostObj->targetType,host_dstFieldId)) {
            ety = dyn_cast<CompositeType>(hostObj->targetType)->getTypeAtIndex(host_dstFieldId);
        }
        Type *expectedPointeeTy = nullptr;
        if (v && v->getType() && v->getType()->isPointerTy()) {
            expectedPointeeTy = v->getType()->getPointerElementType();
        }
#ifdef DEBUG_CREATE_EMB_OBJ
        dbgs() << "createEmbObj(): ety: " << InstructionUtils::getTypeStr(ety) << " expectedPointeeTy: " << InstructionUtils::getTypeStr(expectedPointeeTy) << "\n";
#endif
        if (v) {
            if (!ety || !InstructionUtils::same_types(ety,expectedPointeeTy)) {
#ifdef DEBUG_CREATE_EMB_OBJ
                dbgs() << "createEmbObj(): ety and expectedPointeeTy are different...\n";
#endif
                return nullptr;
            }
        }
        if (hostObj->embObjs.find(host_dstFieldId) != hostObj->embObjs.end()){
            //We have created that embedded object previously.
            newObj = hostObj->embObjs[host_dstFieldId];
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "createEmbObj(): find the previosuly created embed object: " << (const void*)newObj << "\n";
#endif
        }
        if (!newObj || !InstructionUtils::same_types(newObj->targetType,ety)) {
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "createEmbObj(): try to create a new embed object because ";
            if (!newObj) {
                dbgs() << "there is no emb obj in cache...\n";
            }else{
                dbgs() << "the emb obj in cache has a different type than expected: " << InstructionUtils::getTypeStr(newObj->targetType) << "\n";
            }
#endif
            if (newObj) {
                //Erase the parent record of the existing emb obj.
                if (newObj->parent == hostObj) {
#ifdef DEBUG_CREATE_EMB_OBJ
                    dbgs() << "createEmbObj(): try to erase the existing emb obj's parent record since its parent is also this hostObj.\n";
#endif
                    newObj->parent = nullptr;
                    newObj->parent_field = 0;
                }
            }
            //Need to create a new AliasObject for the embedded struct.
            if (v) {
                newObj = DRCHECKER::createOutsideObj(vloc, currPointsTo, false, nullptr);
            }else {
                newObj = DRCHECKER::createOutsideObj(ety, false, nullptr);
            }
            //Properly taint it.
            if(newObj){
#ifdef DEBUG_CREATE_EMB_OBJ
                dbgs() << "createEmbObj(): the embedded obj created: " << (const void*)newObj << " | set is_taint_src to: " << hostObj->is_taint_src << "\n"; 
#endif
                newObj->is_taint_src = hostObj->is_taint_src;
                //This new TargetObject should also be tainted according to the host object taint flags.
                std::set<TaintFlag*> *src_taintFlags = hostObj->getFieldTaintInfo(host_dstFieldId);
                if(src_taintFlags){
#ifdef DEBUG_CREATE_EMB_OBJ
                    dbgs() << "createEmbObj(): try to taint the emb obj, #TaintFlag: " << src_taintFlags->size() << "\n";
#endif
                    for(TaintFlag *currTaintFlag:*src_taintFlags){
                        newObj->taintAllFieldsWithTag(currTaintFlag);
                    }
                }
                //TODO: all contents taint flag.
                //Record it in the "embObjs".
                hostObj->embObjs[host_dstFieldId] = newObj;
                newObj->parent = hostObj;
                newObj->parent_field = host_dstFieldId;
            }else {
#ifdef DEBUG_CREATE_EMB_OBJ
                dbgs() << "createEmbObj(): Failed to create the outside object!\n";
#endif
            }
        }
        return newObj;
    }

    AliasObject *createHostObj(AliasObject *targetObj, Type *hostTy, long field) {
        if (!targetObj || !hostTy || !dyn_cast<CompositeType>(hostTy)) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "createHostObj(): !targetObj || !hostTy || !dyn_cast<CompositeType>(hostTy)\n";
#endif
            return nullptr;
        }
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "createHostObj(): targetObj ty: " << InstructionUtils::getTypeStr(targetObj->targetType) << "\n";
        dbgs() << "createHostObj(): hostObj ty: " << InstructionUtils::getTypeStr(hostTy) << " | " << field << "\n";
#endif
        if (dyn_cast<SequentialType>(hostTy)) {
            field = 0;
        }
        //Have we already created this parent object?
        if (targetObj->parent) {
            if (InstructionUtils::same_types(targetObj->parent->targetType,hostTy) && targetObj->parent_field == field) {
#ifdef DEBUG_CREATE_HOST_OBJ
                dbgs() << "createHostObj(): we have created this parent object before: " << (const void*)(targetObj->parent) << "\n";
#endif
                return targetObj->parent;
            }else {
                //NOTE: we should honor the original parent object, since it's static analysis and we can have multiple pointees for a same pointer
                //and they may have multiple different parent objects, here we're possibly trying yo create a parent object for a wrong pointee, we should
                //just skip.
#ifdef DEBUG_CREATE_HOST_OBJ
                dbgs() << "!!! createHostObj(): found a previously created parent object but w/ different field or type!\n";
                dbgs() << "!!! createHostObj(): previous parent: " << InstructionUtils::getTypeStr(targetObj->parent->targetType) << " | " << targetObj->parent_field << ", id: " << (const void*)targetObj->parent << "\n";
#endif
                return nullptr;
                /*
                if (targetObj->parent->embObjs.find(targetObj->parent_field) != targetObj->parent->embObjs.end()) {
                    targetObj->parent->embObjs[targetObj->parent_field] = nullptr;
                }
                targetObj->parent = nullptr;
                targetObj->parent_field = 0;
                */
            }
        }
        if (!InstructionUtils::isIndexValid(hostTy,field)) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "createHostObj(): field OOB!\n";
#endif
            return nullptr;
        }
        if (!InstructionUtils::same_types(dyn_cast<CompositeType>(hostTy)->getTypeAtIndex(field),targetObj->targetType)) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "createHostObj(): field type doesn't match the host!\n";
#endif
            return nullptr;
        }
        AliasObject *hobj = nullptr;
        if (targetObj->all_contents_taint_flag) {
            std::set<TaintFlag*> *existingTaints = new std::set<TaintFlag*>();
            existingTaints->insert(targetObj->all_contents_taint_flag);
            hobj = DRCHECKER::createOutsideObj(hostTy, true, existingTaints);
        }else{
            hobj = DRCHECKER::createOutsideObj(hostTy, false, nullptr);
        }
        if (!hobj) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "createHostObj(): fail to create the host obj!\n";
#endif
            return nullptr;
        }
        //Setup embed relationship.
        hobj->embObjs[field] = targetObj;
        targetObj->parent = hobj;
        targetObj->parent_field = field;
        return hobj;
    }

    bool matchFieldName(Module *mod, Type *ty, std::string& n, FieldDesc *fd) {
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "matchFieldName(): try to match the field name: " << n << " of type: " << InstructionUtils::getTypeStr(ty) << "\n";
#endif
        if (!ty || !fd || n.size() == 0) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "matchFieldName(): (False) !ty || !fd || n.size() == 0\n";
#endif
            return false;
        }
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "matchFieldName(): FieldDesc: ";
        fd->print_path(dbgs());
#endif
        //Be sure that "ty" exists in the "fd".
        if (fd->findTy(ty) < 0) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "matchFieldName(): (False) no target ty resides at this fd...\n";
#endif
            return false;
        }
        if (fd->host_tys.size() != fd->fid.size()) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "!!! matchFieldName(): (False) #host_tys and #fid mismatch in the fd...\n";
#endif
            return false;
        }
        int i = fd->findHostTy(ty);
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "matchFieldName(): fd->findHostTy(ty): " << i << " #host_tys: " << fd->host_tys.size() << "\n";
#endif
        if (i < ((int)fd->host_tys.size()) - 1) {
            //NOTE that this can also handle the case wherer "i = -1", which means "ty" is the innermost field and its direct host object is host_tys[0].
            std::string fn = InstructionUtils::getStFieldName(mod,dyn_cast<StructType>(fd->host_tys[i+1]),fd->fid[i+1]);
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "matchFieldName(): got the field name: " << fn << "\n";
#endif
            return (fn.size() > 0 && n.find(fn) != std::string::npos);
        }else {
            //It's not a field in a host struct, it's the host struct itself and we don't know its name..
            return false;
        }
        return false;
    }

    int matchFieldsInDesc(Module *mod, Type *ty0, std::string& n0, Type *ty1, std::string& n1, int bitoff, std::vector<FieldDesc*> *fds, std::vector<unsigned> *res) {
        if (!ty0 || !ty1 || !fds || !res) {
            return 0;
        }
        std::vector<unsigned> type_res;
        std::vector<unsigned> prio_res;
        for (int i = 0; i < fds->size(); ++i) {
            FieldDesc *fd = (*fds)[i];
            if (!fd || fd->findTy(ty0) < 0) 
                continue;
            int dstoff = fd->bitoff + bitoff;
            int step = (bitoff > 0 ? 1 : -1);
            for (int j = i; j >= 0 && j < fds->size(); j+=step) {
                if ((*fds)[j]->bitoff == dstoff && (*fds)[j]->findTy(ty1) >= 0) {
                    //Ok, now we're sure that we get a type match for the two fields in the struct, we'll see whether the field names are also matched.
                    //If so, put the matching field id in a special priority queue.
#ifdef DEBUG_CREATE_HOST_OBJ
                    /*
                    dbgs() << "matchFieldsInDesc(): Got a match in current tydesc, n0: " << n0 << ", n1: " << n1 << " ======\n";
                    dbgs() << "Ty0: ";
                    fd->print_path(dbgs());
                    dbgs() << "Ty1: ";
                    (*fds)[j]->print_path(dbgs());
                    */
#endif
                    bool nm_match = false;
                    if (n0.size() > 0 && n1.size() > 0) {
                        nm_match = (matchFieldName(mod,ty0,n0,fd) && matchFieldName(mod,ty1,n1,(*fds)[j]));
                    }else if (n0.size() > 0 || n1.size() > 0) {
                        nm_match = (n0.size() > 0 ? matchFieldName(mod,ty0,n0,fd) : matchFieldName(mod,ty1,n1,(*fds)[j]));
                    }
#ifdef DEBUG_CREATE_HOST_OBJ
                    dbgs() << "matchFieldsInDesc(): nm_match: " << nm_match << "\n";
#endif
                    if (nm_match) {
                        prio_res.push_back(i);
                        prio_res.push_back(j);
                    }
                    type_res.push_back(i);
                    type_res.push_back(j);
                    break;
                }
                if ((step > 0) != ((*fds)[j]->bitoff < dstoff)) {
                    break;
                }
            }
        }
#ifdef DEBUG_CREATE_HOST_OBJ
        if (type_res.size() > 0) {
            dbgs() << "matchFieldsInDesc(): #prio_res: " << prio_res.size() << ", #type_res: " << type_res.size() << "\n";
        }
#endif
        if (prio_res.size() > 0) {
            *res = prio_res;
            return 2;
        }else if (type_res.size() > 0) {
            *res = type_res;
            return 1;
        }
        return 0;
    }

    void sortCandStruct(std::vector<CandStructInf*> *cands, std::set<Instruction*> *insts) {
        if (!cands || !cands->size()) {
            return;
        }
        std::set<Function*> funcs;
        if (insts) {
            for (Instruction *i : *insts) {
                //in case some insts are not inserted into any functions...
                if (i->getParent()) {
                    funcs.insert(i->getFunction());
                }
            }
        }
        for (CandStructInf *c : *cands) {
            std::vector<FieldDesc*> *fds = c->fds;
            FieldDesc *fd0 = (*fds)[c->ind[0]];
            FieldDesc *fd1 = (*fds)[c->ind[1]];
            if (!fd0->host_tys.size()) {
                dbgs() << "!!! sortCandStruct(): No host type inf!\n";
                continue;
            }
            Type *hty = fd0->host_tys[fd0->host_tys.size()-1];
            //If the host type is referred in the target function, then we will have a high confidence.
            for (Function *func : funcs) {
                if (InstructionUtils::isTyUsedByFunc(hty,func)) {
                    c->score += 1000.;
                }
            }
            //TODO: is this reasonable? Is the field name match more important than "used by the function"?
            if (c->field_name_matched) {
                c->score += 1000;
            }
            //TODO: if the type name is similar to the function name, then we will give it a high score.
            //
            /*
            //Observation: it's likely that the #field of ty1 is 0 when "bitoff" is negative. 
            if (c->ind[1] == 0) {
                c->score += 500.;
            }
            */
            //Give a preference to the smaller container..
            c->score -= ((float)(*fds)[fds->size()-1]->bitoff)/100.;
        }
        std::sort(cands->begin(),cands->end(),[](CandStructInf *c0, CandStructInf *c1){
            return (c0->score - c1->score > 0);
        });
        return;
    }

    std::vector<CandStructInf*> *getStructFrom2Fields(DataLayout *dl, Type *ty0, std::string& n0, Type *ty1, std::string& n1, long bitoff, Module *mod) {
        if (!dl || !mod || !ty0 || !ty1) {
            return nullptr;
        }
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "getStructFrom2Fields(): Trying to identify a struct that can match the distanced fields.\n";
#endif
        std::vector<StructType*> tys = mod->getIdentifiedStructTypes();
        std::vector<CandStructInf*> *cands = new std::vector<CandStructInf*>();
        //"prio_cands" records the candidate structs whose field names also match the provided two fields.
        std::vector<CandStructInf*> *prio_cands = new std::vector<CandStructInf*>();
        for (StructType *t : tys) {
            std::vector<FieldDesc*> *tydesc = InstructionUtils::getCompTyDesc(dl,t);
            if (!tydesc) {
                continue;
            }
            //Ok, try to match to given fields w/ a specified distance.
            std::vector<unsigned> res;
            int rc = matchFieldsInDesc(mod,ty0,n0,ty1,n1,bitoff,tydesc,&res);
            if (rc == 0) {
                continue;
            }
#ifdef DEBUG_CREATE_HOST_OBJ
            /*
            dbgs() << "getStructTysFromFieldDistance(): got a match: " << InstructionUtils::getTypeStr(t) << "\n"; 
            for (FieldDesc *fd : *tydesc) {
                fd->print(dbgs());
            }
            */
#endif
            //Ok get a match, record it.
            for (int i = 0; i < res.size(); i += 2) {
                CandStructInf *inf = new CandStructInf();
                inf->fds = tydesc;
                inf->ind.push_back(res[i]);
                inf->ind.push_back(res[i+1]);
                cands->push_back(inf);
                if (rc == 2) {
                    inf->field_name_matched = true;
                    prio_cands->push_back(inf);
                }
            }
        }
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "getStructFrom2Fields(): #cands: " << cands->size() << " #prio_cands: " << prio_cands->size() << "\n";
#endif
        if (prio_cands->size() > 0) {
            return prio_cands;
        }
        return cands;
    }

    //A typical and common scenario in which we need to call this is that in a "GEP i8 *ptr, index" IR the "ptr" points to
    //a certain object but is converted to i8*. then the "index" calculates a pointer pointing outside this object...
    //To find the host obj, what we want to do is to iterate over all struct types in the current module, then find the correct type(s)
    //that has properly distanced field types that matches both the base "ptr" and the pointer type produced by the "GEP" (we need to
    //figure out the true pointer type from the subsequent cast IRs).
    //ARG: "v" points to the location w/ bit offset "bitoff" in the host type "ty".
    //NOTE: this function is time-consuming!
    CandStructInf *inferContainerTy(Module *m,Value *v,Type *ty,long bitoff) {
#ifdef DEBUG_INFER_CONTAINER
        dbgs() << "inferContainerTy(): v: " << InstructionUtils::getValueStr(v) << " ty: " << InstructionUtils::getTypeStr(ty) << " bitoff: " << bitoff << "\n";
#endif
        //We record all failure cases (i.e. cannot find any container objects) in this cache to accelerate future processing,
        //note that we don't set up a 'success' cache because as soon as we find a container, the parent object will be created, thus later
        //bit2Field() has no need to invoke this function again, but failed cases may be queryed again and again.
        static std::map<Value*,std::map<Type*,std::set<long>>> fail_cache;
        if (!m || !v || !ty) {
#ifdef DEBUG_INFER_CONTAINER
            dbgs() << "inferContainerTy(): !m || !v || !ty\n";
#endif
            return nullptr;
        }
        if (fail_cache.find(v) != fail_cache.end() && fail_cache[v].find(ty) != fail_cache[v].end() &&
            fail_cache[v][ty].find(bitoff) != fail_cache[v][ty].end()) {
#ifdef DEBUG_INFER_CONTAINER
            dbgs() << "This is a failed case!\n";
#endif
            return nullptr;
        }
        DataLayout dl = m->getDataLayout();
        //NOTE: use store size here since the host object is on its own (not stored consecutively w/ other same objects).
        long tysz = dl.getTypeStoreSizeInBits(ty);
        //Analyze every OOB GEP w/ the same base pointer "v".
        std::vector<CandStructInf*> cands;
        bool init = true;
        std::set<Instruction*> insts;
        for (User *u : v->users()) {
            if (dyn_cast<Instruction>(u)) {
                //In case this is an instruction artificially created by us.
                if (dyn_cast<Instruction>(u)->getParent()) {
                    insts.insert(dyn_cast<Instruction>(u));
                }else {
                    continue;
                }
            }
            GEPOperator *gep = dyn_cast<GEPOperator>(u);
            //Make sure it's a GEP w/ "v" as the base pointer.
            if (!gep || gep->getPointerOperand() != v) {
                continue;
            }
            int rc;
            long delta = InstructionUtils::calcGEPTotalOffsetInBits(gep,&dl,&rc);
            if (rc) {
                //Cannot calculate the overall offset of this gep.
#ifdef DEBUG_INFER_CONTAINER
                dbgs() << "inferContainerTy(): cannot calculate the overall offset for GEP: " << InstructionUtils::getValueStr(gep) << "\n";
#endif
                continue;
            }
            long resOff = bitoff + delta;
#ifdef DEBUG_INFER_CONTAINER
            dbgs() << "inferContainerTy(): found one GEP using the same srcPointer: " << InstructionUtils::getValueStr(gep) << "\n";
            dbgs() << "inferContainerTy(): delta: " << delta << " resOff: " << resOff << " current host type size: " << tysz << "\n";
#endif
            if (resOff >= 0 && resOff < tysz) {
                //This means current GEP will not index outside the original object, so useless for container inference.
#ifdef DEBUG_INFER_CONTAINER
                dbgs() << "inferContainerTy(): skip since this GEP doesn't access the fields outside current host (i.e. in the container).\n";
#endif
                continue;
            }
            //Try to obtain the real type of this GEP inst by looking at its users, specifically the "cast" and "load" inst.
            Type *ty1 = nullptr;
            std::set<Type*> candTy1;
            for (User *u1 : gep->users()) {
                if (dyn_cast<Instruction>(u1)) {
                    insts.insert(dyn_cast<Instruction>(u1));
                    if (InstructionUtils::isAsanInst(dyn_cast<Instruction>(u1))) {
                        continue;
                    }
                }
                Type *dty = nullptr;
                if (dyn_cast<CastInst>(u1)) {
                    dty = dyn_cast<CastInst>(u1)->getDestTy();
                }else if (dyn_cast<LoadInst>(u1)) {
                    dty = dyn_cast<LoadInst>(u1)->getPointerOperandType();
                }
                if (dty && dty->isPointerTy()) {
                    candTy1.insert(dty->getPointerElementType());
                }
            }
            //Do a simple filtering if there are multiple candidate ty1 types.
            for (Type *t : candTy1) {
                ty1 = t;
                if (dyn_cast<CompositeType>(ty1) || (ty1->isPointerTy() && !ty1->getPointerElementType()->isIntegerTy())) {
                    break;
                }
            }
            if (!ty1) {
#ifdef DEBUG_INFER_CONTAINER
                dbgs() << "inferContainerTy(): cannot find the ty1.\n";
#endif
                continue;
            }
            std::string n0 = "";
            std::string n1 = (gep->hasName() ? gep->getName().str() : "");
#ifdef DEBUG_INFER_CONTAINER
            dbgs() << "inferContainerTy(): ty1: " << InstructionUtils::getTypeStr(ty1) << " n1: " << n1 << "\n";
#endif
            //Ok, now we can get some candidate container types that contain both "ty" and "ty1" with a distance of "resOff".
            std::vector<CandStructInf*> *c = DRCHECKER::getStructFrom2Fields(&dl,ty,n0,ty1,n1,resOff,m);
            //We only reserve those container types that are valid for all GEPs (i.e. intersection).
            if (!c || c->size() == 0) {
                //TODO: directly return nullptr or continue? In theory we should return since it's an intersection but that will
                //immediately cause us to have no container types identified... which is also less likely.
#ifdef DEBUG_INFER_CONTAINER
                dbgs() << "inferContainerTy(): warning: we identified no container types for this ty-ty1-resOff combination...\n";
#endif
                continue;
            }
            if (init) {
                cands = *c;
                init = false;
            }else {
                std::vector<CandStructInf*> tmp_copy = cands;
                cands.clear();
                for (CandStructInf *e : *c) {
                    if (!e) {
                        continue;
                    }
                    if (std::find_if(tmp_copy.begin(),tmp_copy.end(),[e](const CandStructInf *cand) {
                        //NOTE: ind[1] may be different since we consider multiple different GEPs (using the same base ty0) as ty1.
                        return (e->fds == cand->fds && e->ind[0] == cand->ind[0]);
                    }) != tmp_copy.end()) {
                        cands.push_back(e);
                    }
                }
            }
            delete c;
            //We're sure that there must be a correct container type existing in the module, so as long as we have the only available candidate, we should stop and just use it.
            if (cands.size() <= 1) {
                break;
            }
        }
#ifdef DEBUG_INFER_CONTAINER
        dbgs() << "inferContainerTy(): all GEPs analyzed, #cand containers: " << cands.size() << "\n";
#endif
        if (cands.size() == 0) {
            //Add to the fail cache.
            fail_cache[v][ty].insert(bitoff);
            return nullptr;
        }
        //Ok now we have got a candidate container list.
        //We need to select a best candidate to return...
        sortCandStruct(&cands,&insts);
#ifdef DEBUG_INFER_CONTAINER
        /*
        for (int i = 0; i < cands.size(); ++i) {
            Type *t = (*cands[i]->fds)[0]->getOutermostTy();
            dbgs() << "inferContainerTy(): CAND " << i << " SCORE " << cands[i]->score << " : " << InstructionUtils::getTypeStr(t) << "\n"; 
            for (FieldDesc *fd : *cands[i]->fds) {
                fd->print(dbgs());
            }
        }
        */
        for (int i = 0; i < cands.size(); ++i) {
            Type *t = (*cands[i]->fds)[0]->getOutermostTy();
            dbgs() << "inferContainerTy(): ==============CAND " << i << " SCORE " << cands[i]->score << " : " << InstructionUtils::getTypeStr(t) << "\n"; 
            dbgs() << "Ty0: ";
            (*cands[i]->fds)[cands[i]->ind[0]]->print_path(dbgs());
        }
#endif
        //Return the hisghest ranked candidate.
        for (int i = 1; i < cands.size(); ++i) {
            delete cands[i];
        }
        //We need to modify the CandStructInf.ind[0] to make it point to exactly the location of "bitoff" inside "ty",
        //note that currently ind[0] is the location of "ty" in the container.
        int idst = InstructionUtils::locateBitsoffInTyDesc(cands[0]->fds,(*cands[0]->fds)[cands[0]->ind[0]]->bitoff + bitoff);
        if (idst < 0 || idst >= cands[0]->fds->size()) {
            //Add to the fail cache.
            fail_cache[v][ty].insert(bitoff);
            return nullptr;
        }
        cands[0]->ind[0] = idst;
        return cands[0];
    }

    int addToSharedObjCache(OutsideObject *obj) {
#ifdef DEBUG_SHARED_OBJ_CACHE
        dbgs() << "addToSharedObjCache(): for the obj: " << (const void*)obj << " currEntryFunc: " << DRCHECKER::currEntryFunc->getName().str() << "\n";
#endif
        if (!obj || !DRCHECKER::currEntryFunc ||!obj->targetType) {
#ifdef DEBUG_SHARED_OBJ_CACHE
            dbgs() << "addToSharedObjCache(): for the obj: (!obj || !DRCHECKER::currEntryFunc ||!obj->targetType)\n";
#endif
            return 0;
        }
        DRCHECKER::sharedObjCache[obj->targetType][DRCHECKER::currEntryFunc].insert(obj);
        return 1;
    }

    //Ok, now get the "->private" pointee type of the file struct as pointed to by "p".
    //(1) get all GEPs that use the "p" as the base pointer and make the indices (0,16).
    //(2) decide the type of the resulting GEP pointer, by looking at the GEP's users (e.g. a cast inst).
    void probeFilePrivTy(Value *p, std::set<Type*> &retSet) {
        if (!p) {
            return;
        }
        for (User *u : p->users()) {
            GEPOperator *gep = dyn_cast<GEPOperator>(u);
            //Make sure it has a single index.
            if (!gep || gep->getNumOperands() != 3 || gep->getPointerOperand() != p) {
                continue;
            }
            //Get the 2nd constant index value.
            ConstantInt *CI = dyn_cast<ConstantInt>(gep->getOperand(2));
            if (!CI) {
                continue;
            }
            long index = CI->getSExtValue();
            //"16" is a hardcoded index of the ".private" in the file struct.
            if (index != 16) {
                continue;
            }
            //Infer the type from the cast inst of this gep.
            for (User *e : gep->users()) {
                CastInst *cinst = dyn_cast<CastInst>(e);
                if (!cinst || cinst->getOperand(0) != dyn_cast<Value>(gep)) {
                    continue;
                }
                Type *t = cinst->getDestTy();
                //NOTE: the gep itself is a pointer to the file->private, where ->private is also a pointer, so the cast result should be a pointer of a pointer.
                if (t && t->isPointerTy()) {
                    t = t->getPointerElementType();
                    if (t->isPointerTy()) {
                        retSet.insert(t->getPointerElementType());
                    }
                }
            }
        }
        return;
    }

    int AliasObject::maybeAPointee(Value *p) {
        if (!p || !p->getType()) {
            return -1;
        }
        Type *vt = p->getType();
        if (!vt->isPointerTy()) {
            //Since it's not a pointer, we cannot get the type info of the pointee, so conservatively let's return 0.
            return 0;
        }
        Type *pointeeTy = vt->getPointerElementType();
        //i8* or void* can in theory point to anything.
        if (pointeeTy && (pointeeTy->isIntegerTy() || pointeeTy->isVoidTy())) {
            return 0;
        }
        //TODO: For the composite type in theory we need to inspect its type desc, but for now we assume that "p" can point to any composite type,
        //except for some special cases that we will deal with as below.
        //***Special processing for "struct.file" type: match its "->private" pointee object type.
        std::set<Type*> fty0;
        if (pointeeTy && InstructionUtils::same_types(pointeeTy,this->targetType) && dyn_cast<StructType>(pointeeTy)) {
            StructType *stTy = dyn_cast<StructType>(pointeeTy);
            if (stTy->hasName() && stTy->getName().str() == "struct.file") {
                //Ok, it's a file struct, now get the pointee type of "->private" of this AliasObject.
                this->getFieldPointeeTy(16, fty0);
                if (fty0.empty()) {
                    return 0;
                }
            }
        }
        std::set<Type*> fty1;
        probeFilePrivTy(p,fty1);
        for (Type *t0 : fty0) {
            for (Type *t1 : fty1) {
                if (InstructionUtils::same_types(t0,t1)) {
                    return 1;
                }
            }
        }
        return 0;
    }

    OutsideObject *getSharedObjFromCache(Value *v, Type *ty) {
#ifdef DEBUG_SHARED_OBJ_CACHE
        dbgs() << "getSharedObjFromCache(): At the entrance. Type: " << InstructionUtils::getTypeStr(ty) << " currEntryFunc: " << DRCHECKER::currEntryFunc->getName().str() << "\n";
#endif
        if (!ty || !DRCHECKER::currEntryFunc) {
#ifdef DEBUG_SHARED_OBJ_CACHE
            dbgs() << "getSharedObjFromCache(): (!ty || !DRCHECKER::currEntryFunc)\n";
#endif
            return nullptr;
        }
        //TODO: we should use InstructionUtils::same_types() to compare types, instead of ==.
        if (DRCHECKER::sharedObjCache.find(ty) == DRCHECKER::sharedObjCache.end()) {
#ifdef DEBUG_SHARED_OBJ_CACHE
            dbgs() << "getSharedObjFromCache(): No same-typed objs found in the cache.\n";
#endif
            return nullptr;
        }
        OutsideObject *ro = nullptr;
        int max_s = -99;
        for (auto &e : DRCHECKER::sharedObjCache[ty]) {
            if (e.first != DRCHECKER::currEntryFunc) {
                for (OutsideObject *o : e.second) {
#ifdef DEBUG_SHARED_OBJ_CACHE
                    dbgs() << "getSharedObjFromCache(): Cand Obj: " << (const void*)o << " srcEntryFunc: " << e.first->getName().str() << "\n";
#endif
                    if (!v) {
#ifdef DEBUG_SHARED_OBJ_CACHE
                        dbgs() << "getSharedObjFromCache(): Null value, just return this obj.\n";
#endif
                        return o;
                    }else {
                        int t = o->maybeAPointee(v);
#ifdef DEBUG_SHARED_OBJ_CACHE
                        dbgs() << "Possibility Score: " << t << "\n";
#endif
                        if (t > max_s) {
                            max_s = t;
                            ro = o;
                        }
                    }
                }
            }else {
                //This means there is already a same-typed object created previously when analyzing current entry function.
                //TODO: should we re-use this previous obj or create a new one?
#ifdef DEBUG_SHARED_OBJ_CACHE
                dbgs() << "getSharedObjFromCache(): Found a previously created obj by the current entry func.\n";
#endif
            }
        }
#ifdef DEBUG_SHARED_OBJ_CACHE
        dbgs() << "getSharedObjFromCache(): Return Obj: " << (const void*)ro << "\n";
#endif
        return ro;
    }

    int createEmbObjChain(FieldDesc *fd, PointerPointsTo *pto, int limit) {
        if (!fd || !pto || !pto->targetObject) {
#ifdef DEBUG_CREATE_EMB_OBJ_CHAIN
            dbgs() << "createEmbObjChain(): (!fd || !pto || !pto->targetObject)\n";
#endif
            return -1;
        }
        if (fd->fid.size() != fd->host_tys.size() || fd->fid.size() == 0) {
#ifdef DEBUG_CREATE_EMB_OBJ_CHAIN
            dbgs() << "createEmbObjChain(): #fid(" << fd->fid.size() << ") and #host_tys(" << fd->host_tys.size() << ") don't match!\n";
#endif
            return -1;
        }
        int i;
        AliasObject *currHostObj = pto->targetObject;
#ifdef DEBUG_CREATE_EMB_OBJ_CHAIN
        dbgs() << "createEmbObjChain(): limit: " << limit << "\n";
#endif
        for (i = fd->fid.size() - 1; i > std::max(0,limit); --i) {
#ifdef DEBUG_CREATE_EMB_OBJ_CHAIN
            dbgs() << "createEmbObjChain(): current host obj type: " << InstructionUtils::getTypeStr(currHostObj->targetType) << "\n";
            dbgs() << "createEmbObjChain(): Index " << i << ", about to create an embedded obj for: " << InstructionUtils::getTypeStr(fd->host_tys[i]) << " | " << fd->fid[i] << "\n";
#endif
            if (!InstructionUtils::same_types(fd->host_tys[i],currHostObj->targetType)) {
#ifdef DEBUG_CREATE_EMB_OBJ_CHAIN
                dbgs() << "!!! createEmbObjChain(): current host obj type doesn't match the record in the type desc vector, i: " << i << "\n";
#endif
                return i+1;
            }
            pto->targetObject = currHostObj;
            pto->dstfieldId = fd->fid[i];
            AliasObject *newObj = DRCHECKER::createEmbObj(pto->targetObject, fd->fid[i]);
            if (!newObj) {
                //TODO: what to do now...
#ifdef DEBUG_CREATE_EMB_OBJ_CHAIN
                dbgs() << "createEmbObjChain(): fail to get/create the embedded obj!\n";
#endif
                return i;
            }
            currHostObj = newObj;
        }
        if (InstructionUtils::same_types(currHostObj->targetType,fd->host_tys[i])) {
            pto->targetObject = currHostObj;
            pto->dstfieldId = fd->fid[i];
            return i;
        }else {
            return i+1;
        }
        return -1;
    }

    int createHostObjChain(FieldDesc *fd, PointerPointsTo *pto, int limit) {
        if (!fd || !pto || !pto->targetObject) {
#ifdef DEBUG_CREATE_HOST_OBJ_CHAIN
            dbgs() << "createHostObjChain(): (!fd || !pto || !pto->targetObject)\n";
#endif
            return -1;
        }
        if (fd->fid.size() != fd->host_tys.size() || fd->fid.size() == 0) {
#ifdef DEBUG_CREATE_HOST_OBJ_CHAIN
            dbgs() << "createHostObjChain(): #fid(" << fd->fid.size() << ") and #host_tys(" << fd->host_tys.size() << ") don't match!\n";
#endif
            return -1;
        }
        int i = fd->findHostTy(pto->targetObject->targetType);
        for (++i; i < std::min(limit,(int)fd->fid.size()); ++i) {
#ifdef DEBUG_CREATE_HOST_OBJ_CHAIN
            dbgs() << "createHostObjChain(): current sub obj type: " << InstructionUtils::getTypeStr(pto->targetObject->targetType) << "\n";
            dbgs() << "createHostObjChain(): Index " << i << ", about to create its host obj: " << InstructionUtils::getTypeStr(fd->host_tys[i]) << " | " << fd->fid[i] << "\n";
#endif
            AliasObject *hObj = DRCHECKER::createHostObj(pto->targetObject, fd->host_tys[i], fd->fid[i]);
            if (hObj) {
                //Successfully created.
                pto->targetObject = hObj;
                pto->dstfieldId = fd->fid[i];
            }else {
#ifdef DEBUG_CREATE_HOST_OBJ_CHAIN
                dbgs() << "createHostObjChain(): fail to get/create the host obj!\n";
#endif
                return i;
            }
        }
        return i;
    }

    void PointerPointsTo::print(llvm::raw_ostream& OS) {
        if (this->targetObject) {
            OS << InstructionUtils::getTypeStr(this->targetObject->targetType) << " | " << this->dstfieldId << " ,is_taint_src: " << this->targetObject->is_taint_src;
            OS << ", Obj ID: " << (const void*)(this->targetObject) << "\n";
            Value *tv = this->targetObject->getValue();
            if (tv){
                dbgs() << "Inst/Val: " << InstructionUtils::getValueStr(tv) << "\n";
                /*
                if (dyn_cast<Instruction>(tv)){
                    InstructionUtils::printInst(dyn_cast<Instruction>(tv),dbgs());
                }else{
                    dbgs() << InstructionUtils::getValueStr(tv) << "\n";
                }
                */
            }
        }else {
            OS << "Null targetObject!\n";
        }
    }

    bool ObjectPointsTo::inArray(Type *ty) {
        if (!ty || !this->targetObject) {
            return false;
        }
        Type *curHostTy = this->targetObject->targetType;
        if (!curHostTy) {
            return false;
        }
        long fid = this->dstfieldId;
        Type *ety = nullptr;
        if (dyn_cast<CompositeType>(curHostTy)) {
            if (fid) {
                if (InstructionUtils::isIndexValid(curHostTy,fid)) {
                    ety = dyn_cast<CompositeType>(curHostTy)->getTypeAtIndex((unsigned)fid);
                    return (InstructionUtils::same_types(ty,ety) && curHostTy->isArrayTy());
                }else {
                    return false;
                }
            }else {
                ety = dyn_cast<CompositeType>(curHostTy)->getTypeAtIndex((unsigned)0);
                if (InstructionUtils::same_types(ty,curHostTy)) {
                    return (this->targetObject->parent && this->targetObject->parent->targetType && this->targetObject->parent->targetType->isArrayTy());
                }else if (InstructionUtils::same_types(ty,ety)) {
                    return curHostTy->isArrayTy();
                }else {
                    return false;
                }
            }
        }else {
            if (InstructionUtils::same_types(ty,curHostTy)) {
                return (fid == 0 && this->targetObject->parent && this->targetObject->parent->targetType && this->targetObject->parent->targetType->isArrayTy());
            }else {
                return false;
            }
        }
        return false;
    }
}
