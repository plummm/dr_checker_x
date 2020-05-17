//
// Created by machiry on 12/4/16.
//
#include "AliasAnalysisVisitor.h"

namespace DRCHECKER {

#define DEBUG_GET_ELEMENT_PTR
//#define DEBUG_ALLOCA_INSTR
#define DEBUG_CAST_INSTR
//#define DEBUG_BINARY_INSTR
//#define DEBUG_PHI_INSTR
//#define DEBUG_LOAD_INSTR
#define DEBUG_STORE_INSTR
//#define DEBUG_CALL_INSTR
//#define STRICT_CAST
//#define DEBUG_RET_INSTR
//#define FAST_HEURISTIC
//#define MAX_ALIAS_OBJ 50
//hz: Enable creating new outside objects on the fly when the pointer points to nothing.
#define CREATE_DUMMY_OBJ_IF_NULL
#define DEBUG_UPDATE_POINTSTO
//#define AGGRESSIVE_PTO_DUP_FILTER
//#define DEBUG_TMP

    //hz: A helper method to create and (taint) a new OutsideObject.
    OutsideObject* AliasAnalysisVisitor::createOutsideObj(Value *p, bool taint) {
        InstLoc *vloc = new InstLoc(p,this->currFuncCallSites);
        std::map<Value *, std::set<PointerPointsTo*>*> *currPointsTo = this->currState.getPointsToInfo(this->currFuncCallSites);
        //Can we get a same-typed object from the global cache (generated when analyzing another entry function)?
        //NOTE: there are multiple places in the code that create a new OutsideObject, but we onlyd do this multi-entry cache mechanism here,
        //because other places create the object that is related to another object (emb/host/field point-to), while we only need to cache the
        //top-level outside obj here (so that other sub obj can be naturally obtained by the field records inside it).
        if (p && p->getType() && p->getType()->isPointerTy() && dyn_cast<CompositeType>(p->getType()->getPointerElementType())) {
            OutsideObject *obj = DRCHECKER::getSharedObjFromCache(p,p->getType()->getPointerElementType());
            if (obj) {
                //We need to bind the shared object w/ current inst.
                DRCHECKER::updatePointsToRecord(vloc,currPointsTo,obj);
                return obj;
            }
        }
        std::set<TaintFlag*> *existingTaints = nullptr;
        //Need to taint it?
        if (taint) {
            existingTaints = TaintUtils::getTaintInfo(this->currState,this->currFuncCallSites,p);
        }
        OutsideObject *robj = DRCHECKER::createOutsideObj(vloc, currPointsTo, taint, existingTaints);
        if (robj) {
            DRCHECKER::addToSharedObjCache(robj);
        }
        return robj;
    }

    std::set<PointerPointsTo*>* AliasAnalysisVisitor::getPointsToObjects(Value *srcPointer) {
        // Get points to objects set of the srcPointer at the entry of the instruction
        // currInstruction.
        // Note that this is at the entry of the instruction. i.e INFLOW.
        std::map<Value *, std::set<PointerPointsTo*>*>* targetPointsToMap = this->currState.getPointsToInfo(this->currFuncCallSites);
        // Here srcPointer should be present in points to map.
        if(targetPointsToMap->find(srcPointer) != targetPointsToMap->end()) {
            return (*targetPointsToMap)[srcPointer];
        }
        return nullptr;
    }

    bool AliasAnalysisVisitor::isPtoDuplicated(const PointerPointsTo *p0, const PointerPointsTo *p1, bool dbg = false) {
        if (!p0 && !p1) {
            return true;
        }
        if ((!p0) != (!p1)) {
            return false;
        }
        //hz: a simple hack here to avoid duplicated objects.
        if(dbg){
            dbgs() << "----------------------------\n";
        }
        if (p0->dstfieldId != p1->dstfieldId){
            if(dbg){
                dbgs() << "dstField mismatch: " << p0->dstfieldId << "|" << p1->dstfieldId << "\n";
            }
            return false;
        }
        AliasObject *o0 = p0->targetObject;
        AliasObject *o1 = p1->targetObject;
        if(dbg){
            dbgs() << (o0?"t":"f") << (o1?"t":"f") << (o0?(o0->isOutsideObject()?"t":"f"):"n") << (o1?(o1->isOutsideObject()?"t":"f"):"n") << "\n";
        }
        if ((!o0) != (!o1)) {
            return false;
        }
        if (o0 == o1)
            return true;
        //In theory we should return false, except we use a more strict filtering (in order to reduce more points-to records.)
        //By default, the comparison logic is just to see whether the pointee obj and fieldId are the same.
#ifdef AGGRESSIVE_PTO_DUP_FILTER
        //o0 and o1 must be not null now.
        if(dbg){
            dbgs() << "Ty0: " << InstructionUtils::getTypeStr(o0->targetType) << " Ty1: " << InstructionUtils::getTypeStr(o1->targetType) << "\n";
        }
        if(o0->targetType != o1->targetType){
            if(dbg){
                dbgs() << "Target obj type mismatch!\n";
            }
            return false;
        }
        //Ok, now these two points-to have the same target obj type and dst field, what then?
        //We will further look at the object ptr of the target AliasObject, if they are also the same, we regard these 2 objs the same.
        Value *v0 = o0->getObjectPtr();
        Value *v1 = o1->getObjectPtr();
        if(dbg){
            dbgs() << "Ptr0: " << InstructionUtils::getValueStr(v0) << " Ptr1: " << InstructionUtils::getValueStr(v1) << " RES: " << (v0==v1?"T":"F") << "\n";
        }
        return (v0 == v1);
#else
        return false;
#endif
    }

    //Basically we try to see whether the pointee object type matches that of srcPointer, if not, we try adjust the PointerPointsTo, e.g.,
    //by walking through the embed/parent hierarchy of the pointee object.
    //Return: whether the type is matched in the end.
    bool AliasAnalysisVisitor::matchPtoTy(Value *srcPointer, PointerPointsTo *pto) {
        if (!srcPointer || !pto || !pto->targetObject) {
            return false;
        }
        Type *srcTy = srcPointer->getType();
        if (!srcTy || !srcTy->isPointerTy()) {
            return false;
        }
        srcTy = srcTy->getPointerElementType();
        return this->matchPtoTy(srcTy,pto);
    }

    //srcTy is the type we should point to.
    bool AliasAnalysisVisitor::matchPtoTy(Type *srcTy, PointerPointsTo *pto) {
        if (!pto || !pto->targetObject) {
            return false;
        }
        Type *pTy = pto->targetObject->targetType;
        long dstfieldId = pto->dstfieldId;
        if (dstfieldId == 0 && InstructionUtils::same_types(srcTy,pTy)) {
            //Quick path.
            return true;
        }
        if (!srcTy || !pTy) {
            return false;
        }
        //DataLayout *dl = this->currState.targetDataLayout;
        //Ok, first let's see whether srcTy can match the type of any embedded fields in the pto.
        if (dyn_cast<CompositeType>(pTy) && !InstructionUtils::isOpaqueSt(pTy) && InstructionUtils::isIndexValid(pTy,dstfieldId)) {
            Type *eTy = dyn_cast<CompositeType>(pTy)->getTypeAtIndex(dstfieldId);
            //Quick path
            if (InstructionUtils::same_types(eTy,srcTy)) {
                return true;
            }
            FieldDesc *hd = InstructionUtils::getHeadFieldDesc(eTy);
            if (hd && hd->findTy(srcTy) >= 0) {
                //Got a match in the embedded field, try to create the required embedded objects.
#ifdef DEBUG_UPDATE_POINTSTO
                dbgs() << "AliasAnalysisVisitor::matchPtoTy(): We need to adjust the current pto to an embedded field to match the srcPointer!\n";
#endif
                //TODO: +1 or not? +1, we point to target object's parent w/ a specified field, otherwise, we point to the object itself w/ field set to 0.
                int limit = hd->findHostTy(srcTy) + 1;
                //A small hack in order to use "createEmbObjChain".
                hd->host_tys.push_back(pTy);
                hd->fid.push_back(dstfieldId);
                return DRCHECKER::createEmbObjChain(hd,pto,limit) == limit;
            }
        }
        //Then let's see whether the pto has any parent object (e.g. it's embedded in another object) that can match srcTy.
        //NOTE: different than embedded fields, here we are not obligated to create new container object - we only look up the existing ones.
        if (dstfieldId == 0 && dyn_cast<CompositeType>(srcTy) && !InstructionUtils::same_types(srcTy,pTy)) {
            AliasObject *obj = pto->targetObject;
            while (obj && obj->parent && obj->parent_field == 0) {
                obj = obj->parent;
                if (InstructionUtils::same_types(srcTy,obj->targetType)) {
                    //Got the match!
#ifdef DEBUG_UPDATE_POINTSTO
                    dbgs() << "AliasAnalysisVisitor::matchPtoTy(): We need to adjust the current pto to a parent object to match the srcPointer!\n";
#endif
                    pto->targetObject = obj;
                    pto->dstfieldId = 0;
                    return true;
                }
            }
        }
        return false;
    }

    void AliasAnalysisVisitor::updatePointsToObjects(Value *srcPointer, std::set<PointerPointsTo*>* newPointsToInfo) {
        /***
         *  Update the pointsto objects of the srcPointer to newPointstoInfo
         *  At the current instruction.
         *
         *  This also takes care of freeing the elements if they are already present.
         */
#ifdef DEBUG_UPDATE_POINTSTO
        dbgs() << "updatePointsToObjects for : " << InstructionUtils::getValueStr(srcPointer) << "\n";
        dbgs() << "#newPointsToInfo: " << newPointsToInfo->size();
#endif
        if(!newPointsToInfo || newPointsToInfo->size() <= 0){
            //nothing to update.
            return;
        }
#ifdef DEBUG_UPDATE_POINTSTO
        //bool dbg = (newPointsToInfo->size() > 2);
        bool dbg = false;
#else
        bool dbg = false;
#endif
        std::map<Value *, std::set<PointerPointsTo*>*>* targetPointsToMap = this->currState.getPointsToInfo(this->currFuncCallSites);
        auto prevPointsToSet = targetPointsToMap->find(srcPointer);
        //hz: slightly change the logic here in case that "newPointsToInfo" contains some duplicated items.
        if(prevPointsToSet == targetPointsToMap->end()) {
            (*targetPointsToMap)[srcPointer] = new std::set<PointerPointsTo*>();
        }
        prevPointsToSet = targetPointsToMap->find(srcPointer);
        if(prevPointsToSet != targetPointsToMap->end()) {
            // OK, there are some previous values for this
            std::set<PointerPointsTo*>* existingPointsTo = prevPointsToSet->second;
            assert(existingPointsTo != nullptr);
#ifdef DEBUG_UPDATE_POINTSTO
            dbgs() << " #existingPointsTo: " << existingPointsTo->size() << "\n";
#endif
            for(PointerPointsTo *currPointsTo: *newPointsToInfo) {
                // Some basic sanity check.
                if (!currPointsTo || !currPointsTo->targetObject) {
                    continue;
                }
                // for each points to, see if we already have that information, if yes, ignore it.
                if(std::find_if(existingPointsTo->begin(), existingPointsTo->end(), [currPointsTo,dbg,this](const PointerPointsTo *n) {
                    return this->isPtoDuplicated(currPointsTo,n,dbg);
                }) == existingPointsTo->end()) {
                    if(dbg){
                        dbgs() << "############# Inserted!!!\n";
                    }
                    //handle the implicit type cast (i.e. type cast that is not explicitly performed by the 'cast' inst) if any.
                    matchPtoTy(srcPointer,currPointsTo);
#ifdef DEBUG_UPDATE_POINTSTO
                    dbgs() << "Insert point-to: ";
                    currPointsTo->print(dbgs());
#endif
                    existingPointsTo->insert(existingPointsTo->end(), currPointsTo);
                } else {
                    //delete the points to object, as we already have a similar pointsTo object.
                    if(dbg){
                        dbgs() << "############# Duplicated!!!\n";
                    }
                    delete (currPointsTo);
                }
            }
            // delete the set pointer.
            delete(newPointsToInfo);

        } else {
#ifdef DEBUG_UPDATE_POINTSTO
            errs() << "Impossible to reach here...\n";
#endif
            assert(false);
            /*
            dbgs() << " existingPointsTo: 0";
            assert(newPointsToInfo != nullptr);
            if(newPointsToInfo->size() > 0){
                (*targetPointsToMap)[srcPointer] = newPointsToInfo;
            }
            */
        }
#ifdef DEBUG_UPDATE_POINTSTO
        dbgs() << " #After update: " << (*targetPointsToMap)[srcPointer]->size() << "\n";
#endif
    }

    bool AliasAnalysisVisitor::hasPointsToObjects(Value *srcPointer) {
        /***
         * Check if the srcPointer has any pointto objects at currInstruction
         */
        std::map<Value *, std::set<PointerPointsTo*>*>* targetPointsToMap = this->currState.getPointsToInfo(this->currFuncCallSites);
        //Value *strippedPtr = srcPointer->stripPointerCasts();
        return targetPointsToMap != nullptr &&
               targetPointsToMap->find(srcPointer) != targetPointsToMap->end() &&
               (*targetPointsToMap)[srcPointer] &&
               (*targetPointsToMap)[srcPointer]->size();
    }

    //In this version, we assume that "srcPointsTo" points to an embedded struct in a host struct.
    //NOTE: "srcPointer" in this function is related to "srcPointsTo".
    std::set<PointerPointsTo*>* AliasAnalysisVisitor::makePointsToCopy_emb(Instruction *propInstruction, Value *srcPointer, Value *resPointer,
                                                             std::set<PointerPointsTo*>* srcPointsTo, long fieldId, bool is_var_fid) {
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): elements in *srcPointsTo: " << srcPointsTo->size() << " \n";
#endif
        std::set<PointerPointsTo*>* newPointsToInfo = new std::set<PointerPointsTo*>();
        for (PointerPointsTo *currPointsToObj : *srcPointsTo) {
            AliasObject *hostObj = currPointsToObj->targetObject;
            if (!hostObj) {
                continue;
            }
            long dstField = currPointsToObj->dstfieldId;
            Type *host_type = hostObj->targetType;
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): host_type: " << InstructionUtils::getTypeStr(host_type) << " | " << dstField << "\n";
#endif
            //We must ensure that it points to an embedded composite type in another composite.
            if (!host_type || !dyn_cast<CompositeType>(host_type)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): host_type is not composite!\n";
#endif
                continue;
            }
            //Boundary check.
            if (!InstructionUtils::isIndexValid(host_type,dstField)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): invalid dstField for the host_type!\n";
#endif
                continue;
            }
            //Get the dst field type (must be composite) in the host obj.
            Type *ety = dyn_cast<CompositeType>(host_type)->getTypeAtIndex(dstField);
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): ety: " << InstructionUtils::getTypeStr(ety) <<  " | " << fieldId << "\n";
#endif
            if (!ety || !dyn_cast<CompositeType>(ety)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): ety is not a composite field!\n";
#endif
                continue;
            }
            //Variable index check.
            if (is_var_fid) {
                fieldId = 0;
                if (!dyn_cast<SequentialType>(ety)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): got a variable index but the ety is not sequential!\n";
#endif
                    continue;
                }
            }
            //Boundary check.
            if (!InstructionUtils::isIndexValid(ety,fieldId)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): boundary check fails for the ety!\n";
#endif
                continue;
            }
            //Ok, it's an emb struct/array, create new emb object if necessary.
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): trying to get/create an object for the embedded struct/array..\n";
#endif
            AliasObject *newObj = this->createEmbObj(hostObj,dstField,srcPointer);
            if(newObj){
                PointerPointsTo *newPointsToObj = new PointerPointsTo(resPointer,0,newObj,fieldId,new InstLoc(propInstruction,this->currFuncCallSites),false);
                newPointsToInfo->insert(newPointsToInfo->begin(), newPointsToObj);
            }else{
#ifdef DEBUG_GET_ELEMENT_PTR
                errs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): cannot get or create embedded object.\n";
#endif
            }
        }
        return newPointsToInfo;
    }

    AliasObject *AliasAnalysisVisitor::createEmbObj(AliasObject *hostObj, long host_dstFieldId, Value *v) {
        std::map<Value *, std::set<PointerPointsTo*>*> *currPointsTo = this->currState.getPointsToInfo(this->currFuncCallSites);
        return DRCHECKER::createEmbObj(hostObj, host_dstFieldId, new InstLoc(v,this->currFuncCallSites), currPointsTo);
    }

    //NOTE: "is_var_fid" indicates whether the target fieldId is a variable instead of a constant.
    std::set<PointerPointsTo*>* AliasAnalysisVisitor::makePointsToCopy(Instruction *propInstruction, Value *srcPointer,
            std::set<PointerPointsTo*>* srcPointsTo, long fieldId, bool is_var_fid) {
        /***
         * Makes copy of points to information from srcPointer to propInstruction
         */
        std::set<PointerPointsTo*>* newPointsToInfo = new std::set<PointerPointsTo*>();
        // set of all visited objects.
        // to avoid added duplicate pointsto objects
        std::set<AliasObject*> visitedObjects;
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): #elements in *srcPointsTo: " << srcPointsTo->size() << " \n";
#endif
        //"fieldId" will make no sense if "is_var_fid" is set true, we temporarily set "fieldId" to 0 here.
        if (is_var_fid) {
            fieldId = 0;
        }
        //The arg "srcPointer" actually is not related to arg "srcPointsTo", it's indeed "dstPointer" that we need to copy point-to inf for.
        GEPOperator *gep = (srcPointer ? dyn_cast<GEPOperator>(srcPointer) : nullptr);
        //"basePointerType" refers to the type of the pointer operand in the original GEP instruction/opearator, during whose visit we
        //call this makePointsToCopy().
        Type *basePointerType = (gep ? gep->getPointerOperand()->getType() : nullptr);
        Type *basePointToType = (basePointerType ? basePointerType->getPointerElementType() : nullptr);
        for (PointerPointsTo *currPointsToObj : *srcPointsTo) {
            //Try to match the pto w/ the GEP base pointer.
            PointerPointsTo *pto = currPointsToObj->makeCopyP();
            this->matchPtoTy(basePointToType,pto);
            AliasObject *hostObj = pto->targetObject;
            // if the target object is not visited, then add into points to info.
            if(hostObj && visitedObjects.find(hostObj) == visitedObjects.end()) {
                PointerPointsTo *newPointsToObj = new PointerPointsTo();
                newPointsToObj->propogatingInst = new InstLoc(propInstruction,this->currFuncCallSites);
                long host_dstFieldId = pto->dstfieldId;
                //Get type information about current point-to object.
                Type *host_type = hostObj->targetType;
                bool is_emb = false;
                Type *src_ety = nullptr;
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): basePointerType: " << InstructionUtils::getTypeStr(basePointerType) << "\n";
                dbgs() << "Cur Points-to, host_type: " << InstructionUtils::getTypeStr(host_type) << " | " << host_dstFieldId << "\n";
                dbgs() << "hostObj: " << (const void*)hostObj <<  " target field id: " << fieldId << " is_var_fid: " << is_var_fid << "\n";
#endif
                if (!host_type || !InstructionUtils::isIndexValid(host_type,host_dstFieldId)){
                    //TODO: It's unlikely, but is this skip safe?
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): null host type or invalid host_dstFieldId.\n";
#endif
                    goto fail_next;
                }
                if (host_type->isPointerTy()) {
                    host_type = host_type->getPointerElementType();
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): host type to its pointee type: " << InstructionUtils::getTypeStr(host_type) << "\n";
#endif
                }
                //hz: 'dstField' is a complex issue, we first apply original logic to set the default "dstfieldId", then
                //make some modifications if possible:
                //(1) if src pointer points to a non-composite type field in the src object, we simply update "dstField" with the arg "fieldId". (the pointee #field should be 0 in this case...)
                //(2) if the pointee field is of a composite type (e.g. struct or array) in the src object, then the arg "fieldId" indexes into the composite field.
                //Original logic is too simple and error-prone...
                //----------ORIGINAL-----------
                newPointsToObj->fieldId = 0;
                newPointsToObj->targetObject = hostObj;
                newPointsToObj->targetPointer = srcPointer;
                if(fieldId >= 0) {
                    newPointsToObj->dstfieldId = fieldId;
                } else {
                    newPointsToObj->dstfieldId = pto->dstfieldId;
                    //NOTE: fieldId < 0 means that we simply want to copy the passed-in points-to information as is.
                    //TODO: is it possible that we have a negative 1st index?
                    goto update;
                }
                //----------ORIGINAL-----------
                //----------MOD----------
                //Ok, handle two cases here: (1) target field is a composite type (2) host obj is an array.
                if (InstructionUtils::same_types(host_type,basePointToType) && host_dstFieldId == 0) {
                    //The current host object type matches the base pointer, no composite field.
                    //bound check, if fails we discard this point-to, otherwise do nothing.
                    if (!InstructionUtils::isIndexValid(host_type,fieldId)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): host obj matches the base pointer, but the fieldId is invalid...\n";
#endif
                        goto fail_next;
                    }
                    if (is_var_fid && !dyn_cast<SequentialType>(host_type)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): host obj matches the base pointer, but we don't support variable index in the non-sequential host obj.\n";
#endif
                        goto fail_next;
                    }
                }else {
                    //Ok, type mismatch, let's see whether the point-to field type in the host obj matches the base pointer.
                    if (dyn_cast<CompositeType>(host_type)) {
                        src_ety = dyn_cast<CompositeType>(host_type)->getTypeAtIndex(host_dstFieldId);
                    }else {
                        src_ety = host_type;
                    }
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): src_ety: " << InstructionUtils::getTypeStr(src_ety) << "\n";
#endif
                    if (!src_ety || !InstructionUtils::same_types(src_ety,basePointToType)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): src_ety doesn't match the base pointer as well.\n ";
#endif
                        //TODO: Discard it or still update?
                        goto fail_next;
                    }
                    if (!InstructionUtils::isIndexValid(src_ety,fieldId)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): we need to index into the embedded field but the fieldId is invalid for it...\n ";
#endif
                        goto fail_next;
                    }
                    if (is_var_fid && !dyn_cast<SequentialType>(src_ety)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): we need to index into the embedded field but the index is a variable while the src_ety is non-sequential!\n ";
#endif
                        goto fail_next;
                    }
                    //Great, create a new object for the composite field.
                    is_emb = true;
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): index into an embedded struct/array in the host object!\n";
#endif
                    //Ok, the src points to a struct/array embedded in the host object, we cannot just use
                    //the arg "fieldId" as "dstfieldId" of the host object because it's an offset into the embedded struct/array.
                    //We have two candidate methods here:
                    //(1) Create a separate TargetObject representing this embedded struct, then make the pointer operand in original GEP point to it.
                    //(2) Directly create an outside object for the resulted pointer of this GEP. (i.e. the parameter "srcPointer")
                    //Method (1):
                    AliasObject *newObj = this->createEmbObj(hostObj,host_dstFieldId,gep->getPointerOperand());
                    if(newObj){
                        newPointsToObj->targetObject = newObj;
                        newPointsToObj->dstfieldId = fieldId;
                    }else{
                        //We cannot create the new OutsideObject, it's possibly because the target pointer doesn't point to a struct.
                        //In this case, rather than using the original wrong logic, we'd better make it point to nothing.
#ifdef DEBUG_GET_ELEMENT_PTR
                        errs() << "AliasAnalysisVisitor::makePointsToCopy(): cannot get or create embedded object for: " << InstructionUtils::getValueStr(gep->getPointerOperand()) << "\n";
#endif
                        delete newObj;
                        goto fail_next;
                    }
                }
                //----------MOD----------
update:
                if (newPointsToObj){
                    //Insert the points-to info.
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "Assign points-to object: ";
                    if(newPointsToObj->targetObject){
                        dbgs() << InstructionUtils::getTypeStr(newPointsToObj->targetObject->targetType);
                    }
                    dbgs() << " | dstField: " << newPointsToObj->dstfieldId << "\n";
#endif
                    newPointsToInfo->insert(newPointsToInfo->begin(), newPointsToObj);
                }
                visitedObjects.insert(visitedObjects.begin(), hostObj);
                goto next;
fail_next:
                delete newPointsToObj;
                visitedObjects.insert(visitedObjects.begin(), hostObj);
        }//if in visitedObjects
next:
        delete pto;
    }//for
#ifdef DEBUG_GET_ELEMENT_PTR
    dbgs() << "makePointsToCopy: returned newPointsToInfo size: " << newPointsToInfo->size() << "\n";
#endif
    return newPointsToInfo;
}

std::set<PointerPointsTo*>* AliasAnalysisVisitor::mergePointsTo(std::set<Value*> &valuesToMerge, Instruction *targetInstruction, Value *targetPtr) {
    /***
     * Merge pointsToInformation of all the objects pointed by pointers in
     * valuesToMerge
     *
     * targetPtr(if not null) is the pointer that points to all objects in the merge set.
     */
    // Set of pairs of field and corresponding object.
    std::set<std::pair<long, AliasObject*>> targetObjects;
    targetObjects.clear();
    for(Value *currVal:valuesToMerge) {
        // if the value doesn't have points to information.
        // try to strip pointer casts.
        if(!hasPointsToObjects(currVal)) {
            currVal = currVal->stripPointerCasts();
        }
        if(hasPointsToObjects(currVal)) {
            std::set<PointerPointsTo*>* tmpPointsTo = getPointsToObjects(currVal);
            for(PointerPointsTo *currPointsTo:*tmpPointsTo) {
                auto to_check = std::make_pair(currPointsTo->dstfieldId, currPointsTo->targetObject);
                if(std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                    targetObjects.insert(targetObjects.end(), to_check);
                }
            }
        }
    }
    // if there are any objects?
    if (targetObjects.size() > 0) {
        std::set<PointerPointsTo*>* toRetPointsTo = new std::set<PointerPointsTo*>();
        for(auto currItem: targetObjects) {
            PointerPointsTo* currPointsToObj = new PointerPointsTo(targetPtr ? targetPtr : targetInstruction, 0, currItem.second, currItem.first, new InstLoc(targetInstruction,this->currFuncCallSites), false);
            toRetPointsTo->insert(toRetPointsTo->begin(), currPointsToObj);
        }
        return toRetPointsTo;
    }

    return nullptr;
}

std::set<PointerPointsTo*>* AliasAnalysisVisitor::copyPointsToInfo(Instruction *srcInstruction, std::set<PointerPointsTo*>* srcPointsTo) {
    /***
     *  Copy pointsto information from the provided set (srcPointsTo)
     *  to be pointed by srcInstruction.
     */
    std::set<std::pair<long, AliasObject*>> targetObjects;
    targetObjects.clear();
    for(auto currPointsToObj:(*srcPointsTo)) {
        auto to_check = std::make_pair(currPointsToObj->dstfieldId, currPointsToObj->targetObject);
        if(std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
            targetObjects.insert(targetObjects.end(), to_check);
        }
    }

    // if there are any objects?
    if(targetObjects.size() > 0) {
        std::set<PointerPointsTo*>* toRetPointsTo = new std::set<PointerPointsTo*>();
        for(auto currItem: targetObjects) {
            PointerPointsTo* currPointsToObj = new PointerPointsTo(srcInstruction, 0, currItem.second, currItem.first, new InstLoc(srcInstruction,this->currFuncCallSites), false);
            toRetPointsTo->insert(toRetPointsTo->begin(), currPointsToObj);
        }
        return toRetPointsTo;
    }

    return nullptr;

}

void AliasAnalysisVisitor::setLoopIndicator(bool inside_loop) {
    this->inside_loop = inside_loop;
}

void AliasAnalysisVisitor::visitAllocaInst(AllocaInst &I) {
    /***
     *  Visit alloca instruction.
     *  This is the origin of an object
     */
    if(hasPointsToObjects(&I)){
        /*
         * We have already visited this instruction before.
         */
#ifdef DEBUG_ALLOCA_INSTR
        dbgs() << "The Alloca instruction, already processed: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        return;
    }
    AliasObject *targetObj = new FunctionLocalVariable(I, this->currFuncCallSites);
    PointerPointsTo *newPointsTo = new PointerPointsTo(&I, 0, targetObj, 0, new InstLoc(&I,this->currFuncCallSites), false);
    std::set<PointerPointsTo*>* newPointsToInfo = new std::set<PointerPointsTo*>();
    newPointsToInfo->insert(newPointsToInfo->end(), newPointsTo);
#ifdef DEBUG_ALLOCA_INSTR
    dbgs() << "Processed Alloca Instruction, Created new points to information:" << (*newPointsTo) << "\n";
#endif
    this->updatePointsToObjects(&I, newPointsToInfo);

}

void AliasAnalysisVisitor::visitCastInst(CastInst &I) {
    /***
     * This method handles Cast Instruction.
     * First check if we are converting to pointer, if yes, then we need to compute points to
     * If not, check if src value has points to information, if yes, then we need to compute points to
     */
    Type *dstType = I.getDestTy();
    Type *srcType = I.getSrcTy();
    Type *srcPointeeTy = nullptr;
    Type *dstPointeeTy = nullptr;
    if (srcType && srcType->isPointerTy()) {
        srcPointeeTy = srcType->getPointerElementType();
    }
    if (dstType && dstType->isPointerTy()) {
        dstPointeeTy = dstType->getPointerElementType();
    }
    Value *srcOperand = I.getOperand(0);
#ifdef DEBUG_CAST_INSTR
    dbgs() << "AliasAnalysisVisitor::visitCastInst: " << InstructionUtils::getValueStr(&I) << "\n";
    dbgs() << "Convert: " << InstructionUtils::getTypeStr(srcType) << " --> " << InstructionUtils::getTypeStr(dstType) << "\n";
    dbgs() << "srcOperand: " << InstructionUtils::getValueStr(srcOperand) << "\n";
#endif
    // handle inline casting.
    if(!hasPointsToObjects(srcOperand)) {
        srcOperand = srcOperand->stripPointerCasts();
#ifdef DEBUG_CAST_INSTR
        dbgs() << "Src operand doesn't point to any objects, after strip, it becomes: " << InstructionUtils::getValueStr(srcOperand) << "\n";
#endif
    }

    if(hasPointsToObjects(srcOperand)) {
        //In this situation, our overall logic is to propagate all point-to information from the src operand to the dst operand,
        //however, we may have some special processing about the point-to information (e.g. change the type of the point-to obj).
        std::set<PointerPointsTo*>* srcPointsToInfo = getPointsToObjects(srcOperand);
        assert(srcPointsToInfo != nullptr);
        //Create new pointsTo info for the current instruction.
        std::set<PointerPointsTo*>* newPointsToInfo = new std::set<PointerPointsTo*>();
        for(PointerPointsTo *currPointsToObj: *srcPointsToInfo) {
            if (!currPointsToObj->targetObject || !currPointsToObj->targetObject->targetType) {
#ifdef DEBUG_CAST_INSTR
                dbgs() << "AliasAnalysisVisitor::visitCastInst(): null targetObject or null type info!\n";
#endif
                //Discard this point-to.
                continue;
            }
            //NOTE: the "targetObject" will not be copied (only the pointer to it will be copied).
            PointerPointsTo *newPointsToObj = (PointerPointsTo*)currPointsToObj->makeCopy();
            //TODO: do we need to keep the original InstLoc (i.e. that of the pointer to cast)?
            newPointsToObj->propogatingInst = new InstLoc(&I,this->currFuncCallSites);
            newPointsToObj->targetPointer = &I;
            //TODO: this may be unnecessary since the "targetObject" will not be copied.
            newPointsToObj->targetObject->is_taint_src = currPointsToObj->targetObject->is_taint_src;
            Type *currTgtObjType = newPointsToObj->targetObject->targetType;
#ifdef DEBUG_CAST_INSTR
            dbgs() << "AliasAnalysisVisitor::visitCastInst(): current target object: " << InstructionUtils::getTypeStr(currTgtObjType) << " | " << currPointsToObj->dstfieldId << "\n";
#endif
            //--------below are special processings for the point-to information---------
            if (dstPointeeTy) {
                if (dyn_cast<CompositeType>(currTgtObjType)) {
                    //Ok, our src pointer points to a certain field in a certain object, although the pointer value (i.e. address) remains the same, we need to convert
                    //the pointer type, which is because multiple different typed objects can reside at the same location (e.g. heading composite field within the host object).
                    //In this situation we need to modify the point-to objects to the embedded/host object (may need to create new objects when necessary) recursively
                    //(i.e. navigate the object hierarchy at the same location in the type desc vector).
                    std::vector<FieldDesc*> *tydesc = InstructionUtils::getCompTyDesc(this->currState.targetDataLayout, dyn_cast<CompositeType>(currTgtObjType));
                    int i_dstField = InstructionUtils::locateFieldInTyDesc(tydesc, newPointsToObj->dstfieldId);
                    if (i_dstField < 0) {
#ifdef DEBUG_CAST_INSTR
                        dbgs() << "AliasAnalysisVisitor::visitCastInst(): failed to get the dst field type desc!\n";
#endif
                    }else if ((*tydesc)[i_dstField]->fid.size() != (*tydesc)[i_dstField]->host_tys.size()) {
#ifdef DEBUG_CAST_INSTR
                        dbgs() << "AliasAnalysisVisitor::visitCastInst(): #fid and #host_tys don't match!\n";
#endif
                    }else {
                        //Does a same typed object as "dstPointeeTy" already exist?
                        FieldDesc *fd = (*tydesc)[i_dstField];
                        if (fd->findTy(dstPointeeTy) >= 0) {
                            //This means we need to recursively get/create the embedded field objects.
#ifdef DEBUG_CAST_INSTR
                            dbgs() << "AliasAnalysisVisitor::visitCastInst(): try to get/create embedded objects recursively to match the dstPointeeTy.\n";
#endif
                            int limit = fd->findHostTy(dstPointeeTy);
                            //"limit" can be -1 if the dstPointeeTy is not composite, in which case we will create embedded objects for all elements in fd->host_tys.
                            DRCHECKER::createEmbObjChain(fd,newPointsToObj,limit);
                        }else if (dyn_cast<CompositeType>(dstPointeeTy)) {
                            //This means we cannot match the dstPointeeTy inside current host object, we possibly need to create the container object.
                            std::vector<FieldDesc*> *dst_tydesc = InstructionUtils::getCompTyDesc(this->currState.targetDataLayout, dyn_cast<CompositeType>(dstPointeeTy));
                            if (dst_tydesc && dst_tydesc->size() > 0) {
                                FieldDesc *dst_fd = (*dst_tydesc)[0];
                                int i_srcty = dst_fd->findHostTy(currTgtObjType);
                                if (dst_fd->fid.size() == dst_fd->host_tys.size() && dst_fd->findTy(currTgtObjType) >= 0 && i_srcty >= 0) {
                                    DRCHECKER::createHostObjChain(dst_fd, newPointsToObj, dst_fd->fid.size());
                                }else {
#ifdef DEBUG_CAST_INSTR
                                    dbgs() << "AliasAnalysisVisitor::visitCastInst(): dstPointeeTy's type desc is not correct, or it doesn't contain the srcPointeeTy at the head.\n";
#endif
                                }
                            }else {
#ifdef DEBUG_CAST_INSTR
                                dbgs() << "AliasAnalysisVisitor::visitCastInst(): failed to get the type desc for the composite dstPointeeTy.\n";
#endif
                            }
                        }else {
#ifdef DEBUG_CAST_INSTR
                            dbgs() << "AliasAnalysisVisitor::visitCastInst(): dstPointeeTy is not composite and we cannot match it from the type desc of current host object, skip...\n";
#endif
                        }
                    }
                }else /*if (dyn_cast<CompositeType>(currTgtObjType))*/{
                    //This is a little strange since we now have an non-composite AliasObject...
                    //Here we consider a case like a i8* is casted to struct*, where we can directly change the AliasObject's type and taint it properly.
                    //This is often the case for kmalloc'ed() memory region which is initially i8* and then used as a struct storage.
                    if (dstPointeeTy && dyn_cast<CompositeType>(dstPointeeTy)) {
#ifdef DEBUG_CAST_INSTR
                        dbgs() << "AliasAnalysisVisitor::visitCastInst(): casting a non-composite pointer to a composite one, directly change the targetObject's type...\n";
#endif
                        //We also need to re-taint the object (if necessary) since its type has changed.
                        std::set<TaintFlag*> *fieldTaint = newPointsToObj->targetObject->getFieldTaintInfo(0);
                        newPointsToObj->targetObject->reset(&I,dstPointeeTy);
                        //TODO: fieldTaint or all_contents_taint_flag?
                        if (fieldTaint) {
#ifdef DEBUG_CAST_INSTR
                            dbgs() << "AliasAnalysisVisitor::visitCastInst(): trying to re-taint the converted AliasObject, #fieldTaint: " << fieldTaint->size() << "\n";
#endif
                            for (TaintFlag *tf : *fieldTaint) {
                                newPointsToObj->targetObject->taintAllFieldsWithTag(tf);
                            }
                        }
                    }else {
#ifdef DEBUG_CAST_INSTR
                        dbgs() << "AliasAnalysisVisitor::visitCastInst(): try to cast a pointer to a non-composite type to another... simply propagate the point-to.\n";
#endif
                    }
                }
            }else /*if (dstPointeeTy)*/{
#ifdef DEBUG_CAST_INSTR
                dbgs() << "AliasAnalysisVisitor::visitCastInst(): the cast destination is not a pointer, simply propagate the point-to record from src to dst...\n";
#endif
            }
            //--------above are special processings for the point-to information---------
            newPointsToInfo->insert(newPointsToInfo->end(), newPointsToObj);
        }
        // Update the points to Info of the current instruction.
        if (newPointsToInfo->size() > 0) {
            this->updatePointsToObjects(&I, newPointsToInfo);
        }
    }else if (dstType->isPointerTy()) {
        //hz: TODO: do we need to create new OutsideObject here of the dstType?
#ifdef DEBUG_CAST_INSTR
            dbgs() << "WARNING: Trying to cast a value (that points to nothing) to pointer, Ignoring\n";
#endif
            //assert(false);
    }else {
        //This can be a value conversion (e.g. i32 -> i64) that can be ignored.
        //Below is the original Dr.Checker's logic.
        if(!this->inside_loop) {
#ifdef STRICT_CAST
            assert(!srcType->isPointerTy());
#endif
#ifdef DEBUG_CAST_INSTR
            dbgs() << "Ignoring casting as pointer does not point to anything\n";
#endif
        }else {
#ifdef DEBUG_CAST_INSTR
            dbgs() << "Is inside the loop..Ignoring\n";
#endif
        }
    }
}

//hz: make a copy for the src AliasObject of a different type.
AliasObject* AliasAnalysisVisitor::x_type_obj_copy(AliasObject *srcObj, Type *dstType) {
    if (!srcObj || !dstType){
        return nullptr;
    }
    Type *srcType = srcObj->targetType;
#ifdef DEBUG_CAST_INSTR
    dbgs() << "In AliasAnalysisVisitor::x_type_obj_copy, srcObj type: " << InstructionUtils::getTypeStr(srcType);
    dbgs() << " dstType: " << InstructionUtils::getTypeStr(dstType) << "\n";
#endif
    if(!srcType->isStructTy() || !dstType->isStructTy()){
        return nullptr;
    }
    //TODO: Should we add this new obj to the "pointsTo" or "embObjCache" of the parent object of the copied object?
    AliasObject *newObj = srcObj->makeCopy();
    //We are far from done...
    //First, we need to change the object type.
    newObj->targetType = dstType;
    //Then, we need to properly propagate the field taint information.
    //NOTE that the AliasObject member function makeCopy() doesn't copy the field taint information, we need to do it ourselves.
    unsigned srcElemNum = srcType->getStructNumElements();
    unsigned dstElemNum = dstType->getStructNumElements();
    newObj->all_contents_tainted = srcObj->all_contents_tainted;
    newObj->all_contents_taint_flag = srcObj->all_contents_taint_flag;
    newObj->is_taint_src = srcObj->is_taint_src;
    //Copy field taint from src obj to dst obj, but we shouldn't copy taint for fields that don't exist in dst obj.
    for(auto currFieldTaint:srcObj->taintedFields){
        if (currFieldTaint->fieldId < dstElemNum){
            newObj->taintedFields.insert(newObj->taintedFields.end(),currFieldTaint);
        }
    }
    //If srcElemNum < dstElemNum, below code will taint the extra fields automatically when necessary.
    //No worry about repeatedly adding the same taint flags because "taintAllFields" has an existence test for taint flags.
    if (srcObj->all_contents_tainted){
        //Our heuristic is that if src object is all-content-tainted, then possibly we should also treat the dst object as all-field-tainted.
        if (srcObj->all_contents_taint_flag){
            newObj->taintAllFields(srcObj->all_contents_taint_flag);
        }else{
            //Is this possible?
            //TODO
            errs() << "AliasAnalysisVisitor::x_type_obj_copy: all contents tainted but w/o all_contents_taint_flag.\n";
            if (srcElemNum < dstElemNum){
                //We will possibly lose some field taint here, we'd better take a break and see what happened...
                assert(false);
            }
        }
    }
    return newObj;
}

void AliasAnalysisVisitor::visitBinaryOperator(BinaryOperator &I) {
    /***
     *  Handle binary instruction.
     *
     *  get the points to information of both the operands and merge them.
     */

    // merge points to of all objects.
    std::set<Value*> allVals;
    allVals.insert(allVals.end(), I.getOperand(0));
    allVals.insert(allVals.end(), I.getOperand(1));
#ifdef CREATE_DUMMY_OBJ_IF_NULL
    if (!InstructionUtils::isAsanInst(&I)) {
        for (Value *v : allVals) {
            if (!InstructionUtils::isScalar(v) && !hasPointsToObjects(v)) {
                this->createOutsideObj(v,true);
            }
        }
    }
#endif
    std::set<PointerPointsTo*>* finalPointsToInfo = mergePointsTo(allVals, &I);
    if(finalPointsToInfo != nullptr) {
        // Update the points to object of the current instruction.
#ifdef DEBUG_BINARY_INSTR
        dbgs() << "Updating points to information in the binary instruction:";
        I.print(dbgs());
        dbgs() << "\n";
#endif
        this->updatePointsToObjects(&I, finalPointsToInfo);
    } else {
#ifdef DEBUG_BINARY_INSTR
        dbgs() << "No value is a pointer in the binary instruction.";
        I.print(dbgs());
        dbgs() << "\n";
#endif
    }

    // Sanity,
    // it is really weired if we are trying to do a binary operation on 2-pointers
    if(hasPointsToObjects(I.getOperand(0)) && hasPointsToObjects(I.getOperand(1))) {
#ifdef DEBUG_BINARY_INSTR
        dbgs() << "WARNING: Trying to perform binary operation on 2-pointers.";
        I.print(dbgs());
        dbgs() << "\n";
#endif
    }

}

void AliasAnalysisVisitor::visitPHINode(PHINode &I) {
    /***
     *  Merge points to of all objects reaching this phi node.
     */
    // get all values that need to be merged.
    std::set<Value*> allVals;
    for(unsigned i=0;i<I.getNumIncomingValues(); i++) {
        allVals.insert(allVals.end(), I.getIncomingValue(i));
    }
#ifdef CREATE_DUMMY_OBJ_IF_NULL
    /*
    for (Value *v : allVals) {
        if (!InstructionUtils::isScalar(v) && !hasPointsToObjects(v)) {
            this->createOutsideObj(v,true);
        }
    }
    */
#endif

    std::set<PointerPointsTo*>* finalPointsToInfo = mergePointsTo(allVals, &I);
    if(finalPointsToInfo != nullptr) {
        // Update the points to object of the current instruction.
        this->updatePointsToObjects(&I, finalPointsToInfo);
#ifdef DEBUG_PHI_INSTR
        dbgs() << "Merging points to information in the PHI instruction:";
        I.print(dbgs());
        dbgs() << "\n";
#endif
    } else {
#ifdef DEBUG_PHI_INSTR
        dbgs() << "None of the operands are pointers in the PHI instruction:";
        I.print(dbgs());
        dbgs() << "\n";
#endif
    }

}

void AliasAnalysisVisitor::visitSelectInst(SelectInst &I) {
    /***
     *  Merge points to of all objects reaching this select instruction.
     */
    // get all values that need to be merged.
    std::set<Value*> allVals;
    allVals.insert(allVals.end(), I.getTrueValue());
    allVals.insert(allVals.end(), I.getFalseValue());
#ifdef CREATE_DUMMY_OBJ_IF_NULL
    for (Value *v : allVals) {
        if (!InstructionUtils::isScalar(v) && !hasPointsToObjects(v)) {
            this->createOutsideObj(v,true);
        }
    }
#endif

    std::set<PointerPointsTo*>* finalPointsToInfo = mergePointsTo(allVals, &I);
    if(finalPointsToInfo != nullptr) {
        // Update the points to object of the current instruction.
        this->updatePointsToObjects(&I, finalPointsToInfo);
    }

}

    //hz: this method aims to deal with the embedded GEP operator (in "I") in a recursive way.
    //It will try to analyze and record the point-to information in the global state for each GEP operator.
    Value* AliasAnalysisVisitor::visitGetElementPtrOperator(Instruction *I, GEPOperator *gep) {
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::visitGetElementPtrOperator(): " << InstructionUtils::getValueStr(I) << "\n";
        dbgs() << "GEP: " << InstructionUtils::getValueStr(gep) << "\n";
#endif
        //Null pointer or we have processed it before.
        if(!gep || hasPointsToObjects(gep)){
        return gep;
        }
        if(gep->getNumOperands() <= 0 || !gep->getPointerOperand()){
            //What happens...
            return gep;
        }
        //Ok, does it contain another GEP operator as its pointer operand?
        Value* srcPointer = gep->getPointerOperand();
        GEPOperator *op = dyn_cast<GEPOperator>(srcPointer);
        if(op && op->getNumOperands() > 0 && op->getPointerOperand() && !dyn_cast<GetElementPtrInst>(srcPointer)){
            //Do the recursion.
            srcPointer = visitGetElementPtrOperator(I,op);
        }else{
            if(!hasPointsToObjects(srcPointer)) {
                srcPointer = srcPointer->stripPointerCasts();
            }
        }
        //Process the 1st index at first...
        std::set<PointerPointsTo*> *initialPointsTo = this->processGEPFirstDimension(I, gep, srcPointer);
        //Then the remaining indices if any and update the point-to for this GEP.
        this->processMultiDimensionGEP(I, gep, initialPointsTo);
        return gep;
    }

    void AliasAnalysisVisitor::visitGetElementPtrInst(GetElementPtrInst &I) {
        /***
         *  Handle GetElementPtr instruction.
         *  This is tricky instruction.
         *  this is where accessing structure fields happen.
         */
#ifdef TIMING
         auto t0 = InstructionUtils::getCurTime();
#endif
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::visitGetElementPtrInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value* srcPointer = I.getPointerOperand();
        GEPOperator *gep = dyn_cast<GEPOperator>(srcPointer);
        if(gep && gep->getNumOperands() > 0 && gep->getPointerOperand() && !dyn_cast<GetElementPtrInst>(srcPointer)) {
            //hz: recursively deal with the GEP operator.
            srcPointer = visitGetElementPtrOperator(&I,gep);
        } else {
            if(!hasPointsToObjects(srcPointer)) {
                srcPointer = srcPointer->stripPointerCasts();
            }
        }
        //Process the 1st index at first...
        std::set<PointerPointsTo*> *initialPointsTo = this->processGEPFirstDimension(&I, dyn_cast<GEPOperator>(&I), srcPointer);
        //Then the remaining indices if any and update the point-to for this GEP.
        this->processMultiDimensionGEP(&I, dyn_cast<GEPOperator>(&I), initialPointsTo);
#ifdef TIMING
        dbgs() << "[TIMING] AliasAnalysisVisitor::visitGetElementPtrInst(): ";
        InstructionUtils::getTimeDuration(t0,&dbgs());
#endif
    }

    void AliasAnalysisVisitor::processMultiDimensionGEP(Instruction *propInst, GEPOperator *I, std::set<PointerPointsTo*> *srcPointsTo) {
        assert(I);
        if (!I || !srcPointsTo || srcPointsTo->empty()) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processMultiDimensionGEP(): !I || !srcPointsTo || srcPointsTo->empty()\n";
#endif
            return;
        }
        std::set<PointerPointsTo*> todo_set, *final_set = new std::set<PointerPointsTo*>();
        for (PointerPointsTo *pto : *srcPointsTo) {
            if (pto->flag) {
                final_set->insert(pto);
                //one-time use.
                pto->flag = 0;
            } else {
                todo_set.insert(pto);
            }
        }
        if (!todo_set.empty()) {
            std::set<PointerPointsTo*> *currPointsTo = &todo_set;
            bool update = true;
            //We process every index (but still ignore the 1st one) in the GEP, instead of the only 2nd one in the original Dr.Checker.
            for (int i=2; i<I->getNumOperands(); ++i) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "About to process index: " << (i-1) << "\n";
#endif
                ConstantInt *CI = dyn_cast<ConstantInt>(I->getOperand(i));
                unsigned long structFieldId = 0;
                bool is_var_fid = false;
                if (!CI) {
                    is_var_fid = true;
                }else {
                    structFieldId = CI->getZExtValue();
                }
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "Index value: " << structFieldId << " is_var_fid: " << is_var_fid << "\n";
#endif
                //Loop invariant: "currPointsTo" always has contents here.
                std::set<PointerPointsTo*>* newPointsToInfo = nullptr;
                if (i > 2) {
                    //More than 2 indices in this GEP, according to the GEP specification, this means the last (i-1) index
                    //must index into an embedded struct, instead of a pointer field.
                    //TODO: operator vs. inst
                    Value *subGEP = InstructionUtils::createSubGEP(I,i-1);
                    Value *resGEP = nullptr;
                    if (i >= I->getNumOperands()-1) {
                        resGEP = I;
                    }else {
                        resGEP = InstructionUtils::createSubGEP(I,i);
                    }
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "subGEP: " << InstructionUtils::getValueStr(subGEP) << "\n";
                    dbgs() << "resGEP: " << InstructionUtils::getValueStr(resGEP) << "\n";
#endif
                    if (subGEP) {
                        newPointsToInfo = makePointsToCopy_emb(propInst, subGEP, resGEP, currPointsTo, structFieldId, is_var_fid);
                    }
                }else {
                    //Most GEP should only have 2 indices..
                    newPointsToInfo = makePointsToCopy(propInst, I, currPointsTo, structFieldId, is_var_fid);
                }
                if (!newPointsToInfo || newPointsToInfo->empty()) {
                    //Fallback: just update w/ the "currPointsTo" except when this is a 2-dimension GEP.
                    if (i == 2) {
                        update = false;
                    }
                    break;
                }
                currPointsTo = newPointsToInfo;
            }
            if (update && currPointsTo && !currPointsTo->empty()) {
                final_set->insert(currPointsTo->begin(),currPointsTo->end());
            }
        }
        if (!final_set->empty()) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processMultiDimensionGEP(): updating the point-to for current GEP...\n";
#endif
            //make sure the points-to information includes the correct TargetPointer, which is current GEP inst.
            //TODO: is this ok? Since the pointsTo->targetPointer may not be the "I", it may be a GEP with a subset of indices created by us.
            for (PointerPointsTo *pointsTo : *final_set) {
                pointsTo->targetPointer = I;
            }
            this->updatePointsToObjects(I, final_set);
        }else {
            delete(final_set);
        }
    }

    //Analyze the 1st dimension of the GEP (the arg "I") and return a point-to set of the 1st dimension.
    //NOTE: we assume that "srcPointer" has already been processed regarding inlined GEP operator and strip by the caller.
    std::set<PointerPointsTo*> *AliasAnalysisVisitor::processGEPFirstDimension(Instruction *propInst, GEPOperator *I, Value *srcPointer) {
        //First try to get the point-to of the srcPointer..
        if (!I || !srcPointer) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): Null I or srcPointer..\n";
#endif
            return nullptr;
        }
#ifdef CREATE_DUMMY_OBJ_IF_NULL
        //hz: try to create dummy objects if there is no point-to information about the pointer variable,
        //since it can be an outside global variable. (e.g. platform_device).
        //TODO: are there any ASAN inserted GEP insts and do we need to exclude them?
        if (!hasPointsToObjects(srcPointer)) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): Try to create an OutsideObject for srcPointer: " << InstructionUtils::getValueStr(srcPointer) << "\n";
#endif
            this->createOutsideObj(srcPointer,true);
        }
#endif
        if (!hasPointsToObjects(srcPointer)) {
            //No way to sort this out...
#ifdef DEBUG_GET_ELEMENT_PTR
            errs() << "AliasAnalysisVisitor::processGEPFirstDimension(): No points-to for: " << InstructionUtils::getValueStr(srcPointer) << ", return\n";
#endif
            return nullptr;
        }
        std::set<PointerPointsTo*> *basePointsTo = getPointsToObjects(srcPointer);
        //Make a copy of the basePointsTo
        std::set<PointerPointsTo*> *srcPointsTo = new std::set<PointerPointsTo*>();
        for (PointerPointsTo *p : *basePointsTo) {
            if (!p) {
                continue;
            }
            PointerPointsTo *np = p->makeCopyP();
            np->propogatingInst = new InstLoc(propInst,this->currFuncCallSites);
            np->targetPointer = I;
            srcPointsTo->insert(np);
        }
        //Get the original pointer operand used in this GEP and its type info.
        Value *orgPointer = I->getPointerOperand();
        if (!orgPointer) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): Null orgPointer..return\n";
#endif
            return nullptr;
        }
        Type *basePointerTy = orgPointer->getType();
        Type *basePointeeTy = nullptr;
        if (basePointerTy && basePointerTy->isPointerTy()) {
            basePointeeTy = basePointerTy->getPointerElementType();
        }
        //Get the 1st dimension, note that we can only process the constant dimension.
        ConstantInt *CI = dyn_cast<ConstantInt>(I->getOperand(1));
        if (!CI) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): Non-constant 0st index!\n";
#endif
            //The logic here is that if the base pointer is of an integer pointer type, that means it will possibly do some pointer
            //arithmetics w/ a variable offset, in which case we don't know anything about the result pointee, so we just return nullptr.
            //If it's not an integer pointer, then possibly it's a struct pointer and the first variable index intends to retrieve a
            //struct element from an array, so we just return the original point-to (i.e. collapse the whole array to one element).
            if (basePointeeTy && dyn_cast<IntegerType>(basePointeeTy)) {
                return nullptr;
            }else {
                return srcPointsTo;
            }
        }
        long index = CI->getSExtValue();
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension():: basePointeeTy: " << InstructionUtils::getTypeStr(basePointeeTy) << " 0st index: " << index << "\n";
#endif
        std::set<PointerPointsTo*> *resPointsTo = new std::set<PointerPointsTo*>();
        DataLayout *dl = this->currState.targetDataLayout;
        if (basePointeeTy && dl && index) {
            bool is_primitive = InstructionUtils::isPrimitiveTy(basePointeeTy);
            //NOTE: we use alloc size here since 1st GEP index is intended to index an array of the basePointeeTy (i.e. the basePointeeTy will be stored consecutively so we need its alloc size).
            unsigned width = dl->getTypeAllocSizeInBits(basePointeeTy);
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): basePointeeTy size: " << width << ", is_primitive: " << is_primitive << "\n";
#endif
            for (PointerPointsTo *currPto : *srcPointsTo) {
                if (!currPto || !currPto->targetObject) {
                    //In this case we will exclude this point-to record in the "resPointsTo" to be returned..
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): !currPto || !currPto->targetObject\n";
#endif
                    continue;
                }
                //The "newPto" will be the point-to record after we process the 1st dimension.
                //By default it will the same as the original point-to.
                PointerPointsTo *newPto = new PointerPointsTo(I, 0, currPto->targetObject, currPto->dstfieldId, new InstLoc(propInst,this->currFuncCallSites), false);
                //Type match in the object parent/embed hierarchy.
                bool ty_match = matchPtoTy(basePointeeTy,newPto);
                if (newPto->inArray(basePointeeTy)) {
                    //We will not invoke bit2Field() to do the pointer arithmetic in one situation: host object is an array of the basePointeeTy (i.e. we are array-insensitive).
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): ignore the 1st index since we're in an array.\n";
#endif
                    resPointsTo->insert(newPto);
                } else {
                    if (!is_primitive) {
                        //The 1st index is not for an array, instead it's for pointer arithmetic, this usually only happens when the GEP base pointee is primitive (e.g. i8)
                        //in which case the GEP has just one index, but now we have a non-primitive base pointer for pointer arithmetic (and the GEP can have multiple indices)...
                        //What we do here is we convert this GEP to a one-index GEP w/ primitive base pointee, by calculating the overall bit offset of this multi-index GEP. 
                        int rc;
                        index = InstructionUtils::calcGEPTotalOffsetInBits(I,dl,&rc);
                        if (rc) {
                            //This means we fail to calculate the total offset of current GEP... No way to handle it then.
#ifdef DEBUG_GET_ELEMENT_PTR
                            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): fail to get the total offset of current non-primitive GEP to handle the non-zero 1st index...\n";
#endif
                            continue;
                        }
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): calculated offset sum in bits: " << index << "\n";
#endif
                        width = 1; //bit unit.
                        //Tell the visitGEP() that it doesn't need to process the remainig indices (if any) since we have converted this GEP to single-index for this pto.
                        newPto->flag = 1;
                    }
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): invoke bit2Field()...\n";
#endif
                    if (!this->bit2Field(propInst,I,newPto,width,index)) {
                        resPointsTo->insert(newPto);
                    }
                }
            }
        } else {
            return srcPointsTo;
        }
        //release the memory of "srcPointsTo"
        for (PointerPointsTo *p : *srcPointsTo) {
            delete(p);
        }
        delete(srcPointsTo);
        return resPointsTo;
    }

    //Starting from "dstfieldId" in the target object (struct) as specified in "pto", if we step bitWidth*index bits, which field will we point to then?
    //The passed-in "pto" will be updated to point to the resulted object and field. (e.g. we may end up reaching a field in an embed obj in the host obj).
    //NOTE: we assume the "pto" has been verified to be a struct pointer.
    int AliasAnalysisVisitor::bit2Field(Instruction *propInst, GEPOperator *I, PointerPointsTo *pto, unsigned bitWidth, long index) {
        if (index == 0) {
            return 0;
        }
        DataLayout *dl = this->currState.targetDataLayout;
        if (!dl || !pto) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): !dl || !pto\n";
#endif
            //We'll lose the point-to in this case.
            return -1;
        }
        long dstOffset = 0, resOffset = 0, bits = 0, org_bits = (long)bitWidth * index, org_dstOffset = 0;
        std::vector<FieldDesc*> *tydesc = nullptr;
        int i_dstfield = 0;
        AliasObject *targetObj = nullptr;
        Type *targetObjTy = nullptr;
        while(true) {
            targetObj = pto->targetObject;
            long dstfield = pto->dstfieldId;
            targetObjTy = targetObj->targetType;
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): host obj: " << InstructionUtils::getTypeStr(targetObjTy) << " | " << dstfield << " obj ID: " << (const void*)targetObj << "\n";
#endif
            if (!targetObjTy || !dyn_cast<CompositeType>(targetObjTy)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::bit2Field(): not a composite host type, return...\n";
#endif
                return -1;
            }
            //Boundary check.
            if (!InstructionUtils::isIndexValid(targetObjTy,dstfield)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::bit2Field(): dstfield out-of-bound.\n";
#endif
                return -1;
            }
            tydesc = InstructionUtils::getCompTyDesc(dl,dyn_cast<CompositeType>(targetObjTy));
            if (!tydesc) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): we cannot get the detailed type desc for current host obj, return...\n";
#endif
                return -1;
            }
            i_dstfield = InstructionUtils::locateFieldInTyDesc(tydesc,dstfield);
            if (i_dstfield < 0) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): we cannot locate the dst field desc in the type desc vector, return...\n";
#endif
                return -1;
            }
            //NOTE: both "dstOffset" and "bits" can be divided by 8, "bits" can be negative.
            dstOffset = (*tydesc)[i_dstfield]->bitoff;
            org_dstOffset += dstOffset;
            bits = index * (long)bitWidth;
            resOffset = dstOffset + bits;
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): dstOffset(org_dstOffset): " << dstOffset << "(" << org_dstOffset << ")";
            dbgs() << " bits(org_bits): " << bits << "(" << org_bits << ")" << " resOffset: " << resOffset << "\n";
#endif
        	//NOTE: llvm DataLayout class has three kinds of type size:
        	//(1) basic size, for a composite type, this is the sum of the size of each field type.
        	//(2) store size, a composite type may need some paddings between its fields for the alignment.
        	//(3) alloc size, two successive composite types may need some paddings between each other for alignment.
        	//For our purpose, we need the real size for a single type, so we use "store size", note that if the type is array, "store size" already takes the padding
        	//between each element into account.
            if (resOffset < 0 || (uint64_t)resOffset >= dl->getTypeStoreSizeInBits(targetObjTy)) {
                //This is possibly the case of "container_of()" where one tries to access the host object from within the embedded object,
                //what we should do here is try to figure out what's the host object and adjust the point-to accordingly.
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::bit2Field(): resOffset (in bits) out-of-bound, possibly the container_of() case, trying to figure out the host object...\n";
#endif
				if (targetObj->parent && targetObj->parent->targetType) {
                    //Ok, parent object on file.
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::bit2Field(): parent object on file, try it..\n";
#endif
                    pto->targetObject = targetObj->parent;
                    pto->dstfieldId = targetObj->parent_field;
                    bitWidth = 1;
                    index = resOffset;
                }else {
                    break;
                }
            }else {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::bit2Field(): current container object can satisfy the result offset!\n";
#endif
                break;
            }
        }
        //Have we got the parent object that can hold the resOffset?
        if (resOffset < 0 || (uint64_t)resOffset >= dl->getTypeStoreSizeInBits(pto->targetObject->targetType)) {
            //No.. We need infer the container type...
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): the recorded parent object is not enough, we need to infer the unknown container object...\n";
#endif
            //We cannot use "dstOffset" here, we should use the realDstOffset of the original GEP base pointer...
            CandStructInf *floc = DRCHECKER::inferContainerTy(propInst->getModule(),I->getPointerOperand(),pto->targetObject->targetType,org_dstOffset);
            if (!floc || !floc->fds || floc->ind[0] < 0 || floc->ind[0] >= floc->fds->size()) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::bit2Field(): failed to infer the container type...\n";
#endif
                return -1;
            }
            //Check whether the container can contain the target offset (in theory this should already been verified by inferContainerTy())
            tydesc = floc->fds;
            i_dstfield = floc->ind[0];
            dstOffset = (*tydesc)[i_dstfield]->bitoff;
            resOffset = dstOffset + org_bits;
            targetObjTy = (*tydesc)[0]->host_tys[(*tydesc)[0]->host_tys.size()-1];
            if (resOffset < 0 || (uint64_t)resOffset >= dl->getTypeStoreSizeInBits(targetObjTy)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): the inferred container object still cannot hold the target bitoff...\n";
#endif
                return -1;
            }
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): successfully identified the container object, here is the FieldDesc of the original pointee bitoff:\n";
            (*tydesc)[i_dstfield]->print(dbgs());
            dbgs() << "AliasAnalysisVisitor::bit2Field(): dstOffset: " << dstOffset << " bits: " << org_bits << " resOffset: " << resOffset << "\n";
#endif
            //Ok, we may need to create the host object chain for the location pointed to by the GEP base pointer if necessary.
            int limit = (*tydesc)[i_dstfield]->host_tys.size();
            DRCHECKER::createHostObjChain((*tydesc)[i_dstfield],pto,limit);
            if (!InstructionUtils::same_types(pto->targetObject->targetType,targetObjTy)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): incomplete creation of the host obj chain.\n";
#endif
                return -1;
            }
        }
        //Ok, now we are sure that the target "resOffset" will not exceed the current host object since we've created all container objects by desire.
        //Next, we need to see whether this "resOffset" is inside an embedded composite typed field within the container object, and recursively create the embedded object when necessary.
        int i_resoff = InstructionUtils::locateBitsoffInTyDesc(tydesc,resOffset);
        if (i_resoff < 0) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): Cannot locate the resOffset in the type desc, return...\n";
#endif
            return -1;
        }
        FieldDesc *fd = (*tydesc)[i_resoff];
        if (fd->fid.size() != fd->host_tys.size()) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): fd->fid.size() != fd->host_tys.size()\n";
#endif
            return -1;
        }
        int limit = -1;
        //NOTE: at a same bit offset there can be a composite field who recursively contains multiple composite sub-fields at its head:
        // e.g. [[[   ]    ]     ], in this case the type desc will record all these sub composite fields at the head and all #fid is 0,
        //while we don't really want to create the embedded object up to the innermost heading composite field, instead we stop at the outermost
        //head composite field here.
        while (++limit < fd->fid.size() && !fd->fid[limit]);
        int r = DRCHECKER::createEmbObjChain(fd,pto,limit);
        if (r > limit) {
            //There must be something wrong in the createEmbObjChain()...
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): something wrong w/ the createEmbObjChain(), point-to result will be unreliable, discard..\n";
#endif
            return -1;
        }
        return 0;
    }

    //NOTE: this function wraps the logic of the original Dr.Checker to process GEP w/ only one index/dimension.
    void AliasAnalysisVisitor::processOneDimensionGEP(Instruction *propInst, GEPOperator *I) {
        if (!I) {
            return;
        }
        if (I->getNumOperands() > 2) {
            return;
        }
        for(int i=0;i<I->getNumOperands();i++) {
            if(dyn_cast<Constant>(I->getOperand(i))) {
                continue;
            }
            Value *srcPointer = I->getOperand(i);

#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "GEP instruction for array, operand: " << i << " srcPointer: " << InstructionUtils::getValueStr(srcPointer) << "\n";
#endif

            // OK, we are not indexing a struct. This means, we are indexing an array
            //ConstantInt *CI = dyn_cast<ConstantInt>(I.getOperand(1));
            // OK, we are trying to access an array, first number should be constant, actually it should be zero

            // are we incrementing pointer? if yes, then index 1 may not be constant.
            /*if (I.getNumOperands() > 2) {
              assert(CI != nullptr);
              }*/
            //dbgs() << "CURRINST:" << I << "\n";
            //for (int i = 0; i < I.getNumOperands(); i++) {
            //dbgs() << "Oper:" << *(I.getOperand(i)) << "\n";
            //}

            // we could have array operand as first operand, rather than pointer operand.
            // array operand could be at end
            if (!hasPointsToObjects(srcPointer)) {
                // check if this is the array operand.
                // srcPointer = I->getOperand(1);
                if (!hasPointsToObjects(srcPointer)) {
                    srcPointer = srcPointer->stripPointerCasts();
                }
            }
            //Ignore the index.
#ifdef CREATE_DUMMY_OBJ_IF_NULL
            //hz: try to create dummy objects if there is no point-to information about the pointer variable,
            //since it can be an outside global variable. (e.g. platform_device).
            if(!hasPointsToObjects(srcPointer)) {
                this->createOutsideObj(srcPointer,true);
            }
#endif
            if (hasPointsToObjects(srcPointer)) {
                std::set<PointerPointsTo *> *srcPointsTo = getPointsToObjects(srcPointer);
                std::set<PointerPointsTo *> *newPointsToInfo = makePointsToCopy(propInst, I, srcPointsTo, -1);
                if(newPointsToInfo && !newPointsToInfo->empty()){
                    this->updatePointsToObjects(I, newPointsToInfo);
                }
                break;
            } else {
                // we are trying to dereference an array
                // however the src pointer does not point to any object.
                // How sad??
#ifdef DEBUG_GET_ELEMENT_PTR
                errs() << "Array pointer does not point to any object: " << InstructionUtils::getValueStr(srcPointer) << " Ignoring.\n";
#endif
                //assert(false);
            }
        }
    }

    void AliasAnalysisVisitor::visitLoadInst(LoadInst &I) {

#ifdef TIMING
        auto t0 = InstructionUtils::getCurTime();
#endif
#ifdef DEBUG_LOAD_INSTR
        errs() << "AliasAnalysisVisitor::visitLoadInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value* srcPointer = I.getPointerOperand();
        GEPOperator *gep = dyn_cast<GEPOperator>(I.getPointerOperand());
        if(gep && gep->getNumOperands() > 0 && gep->getPointerOperand() && !dyn_cast<GetElementPtrInst>(I.getPointerOperand())) {
#ifdef DEBUG_LOAD_INSTR
            errs() << "AliasAnalysisVisitor::visitLoadInst(): There is a GEP operator: " << InstructionUtils::getValueStr(gep) << "\n";
#endif
            //srcPointer = gep->getPointerOperand();
            //hz: to get the field sensitive point-to information and record it for the GEP operator value.
            srcPointer = visitGetElementPtrOperator(&I,gep);
        } else {
            if(!hasPointsToObjects(srcPointer)) {
                srcPointer = srcPointer->stripPointerCasts();
#ifdef DEBUG_LOAD_INSTR
                errs() << "AliasAnalysisVisitor::visitLoadInst(): No point-to info, after stripping the pointer casts -0, srcPointer: " << InstructionUtils::getValueStr(srcPointer) << "\n";
#endif
            }
        }

        // strip pointer casts. if we cannot find any points to for the srcPointer.
        if(!hasPointsToObjects(srcPointer)) {
            srcPointer = srcPointer->stripPointerCasts();
#ifdef DEBUG_LOAD_INSTR
            errs() << "AliasAnalysisVisitor::visitLoadInst(): No point-to info, after stripping the pointer casts -1, srcPointer: " << InstructionUtils::getValueStr(srcPointer) << "\n";
#endif
        }

#ifdef CREATE_DUMMY_OBJ_IF_NULL
        //hz: try to create dummy objects if there is no point-to information about the pointer variable,
        //since it can be an outside global variable. (e.g. platform_device).
        if(!InstructionUtils::isAsanInst(&I) && !hasPointsToObjects(srcPointer)) {
            this->createOutsideObj(srcPointer,true);
        }
#endif

        if(!hasPointsToObjects(srcPointer)) {
#ifdef DEBUG_LOAD_INSTR
            errs() << "AliasAnalysisVisitor::visitLoadInst(): srcPointer does not point to any object.\n";
#endif
            return;
        }

        // srcPointer should have pointsTo information.
        //assert(hasPointsToObjects(srcPointer));

        // Get the src points to information.
        std::set<PointerPointsTo*>* srcPointsTo = getPointsToObjects(srcPointer);
        // OK, now what? :)
        // Get all objects pointed by all the objects in the srcPointsTo

        // this set stores the <fieldid, targetobject> of all the objects to which the srcPointer points to.
        std::set<std::pair<long, AliasObject*>> targetObjects;
        for(PointerPointsTo *currPointsToObj:*srcPointsTo) {
            long target_field = currPointsToObj->dstfieldId;
            AliasObject* dstObj = currPointsToObj->targetObject;
            auto to_check = std::make_pair(target_field, dstObj);
            if(std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                targetObjects.insert(targetObjects.end(), to_check);
            }
        }
#ifdef DEBUG_LOAD_INSTR
        dbgs() << "Number of target objects:" << targetObjects.size() << "\n";
#endif


        // Now get the list of objects to which the fieldid of the corresponding object points to.
        std::set<std::pair<long,AliasObject*>> finalObjects;
        finalObjects.clear();
        InstLoc *propInst = new InstLoc(&I,this->currFuncCallSites);
        for(const std::pair<long, AliasObject*> &currObjPair : targetObjects) {
            // fetch objects that could be pointed by the field.
            // if this object is a function argument then
            // dynamically try to create an object, if we do not have any object
            currObjPair.second->fetchPointsToObjects(currObjPair.first, finalObjects, propInst, finalObjects.empty());
        }
        if(finalObjects.size() > 0) {
#ifdef FAST_HEURISTIC
            if(finalObjects.size() > MAX_ALIAS_OBJ) {
                auto end = std::next(finalObjects.begin(), std::min((long)MAX_ALIAS_OBJ, (long)finalObjects.size()));
                std::set<std::pair<long,AliasObject*>> tmpList;
                tmpList.clear();
                tmpList.insert(finalObjects.begin(), end);
                finalObjects.clear();
                finalObjects.insert(tmpList.begin(), tmpList.end());
            }
#endif
            // Create new pointsTo set and add all objects of srcPointsTo
            std::set<PointerPointsTo*>* newPointsToInfo = new std::set<PointerPointsTo*>();
            for(auto currPto:finalObjects) {
                PointerPointsTo *newPointsToObj = new PointerPointsTo(&I, 0, currPto.second, currPto.first, new InstLoc(&I,this->currFuncCallSites), false);
                newPointsToInfo->insert(newPointsToInfo->end(), newPointsToObj);
            }
            // Just save the newly created set as points to set for this instruction.
            this->updatePointsToObjects(&I, newPointsToInfo);
        } else {
            // points to set is empty.
            // Make sure that we are not trying to load a pointer.
            if(!this->inside_loop) {
                //hz: if we reach here, possibly the previously stripped pointer is incorrect,
                //instead of the assert, we'd better ignore this and hope later analysis can create an OutsideObject for current LoadInst.
                //assert(!I.getType()->isPointerTy());
            }
        }
#ifdef TIMING
        dbgs() << "[TIMING] AliasAnalysisVisitor::visitLoadInst(): ";
        InstructionUtils::getTimeDuration(t0,&dbgs());
#endif
    }

    void AliasAnalysisVisitor::visitStoreInst(StoreInst &I) {
#ifdef TIMING
        auto t0 = InstructionUtils::getCurTime();
#endif
#ifdef DEBUG_STORE_INSTR
        dbgs() << "AliasAnalysisVisitor::visitStoreInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value *targetPointer = I.getPointerOperand();
        GEPOperator *gep = dyn_cast<GEPOperator>(I.getPointerOperand());
        if(gep && gep->getNumOperands() > 0 && gep->getPointerOperand() && !dyn_cast<GetElementPtrInst>(I.getPointerOperand())) {
#ifdef DEBUG_STORE_INSTR
            dbgs() << "There is a GEP operator for targetPointer: " << InstructionUtils::getValueStr(gep) << "\n";
#endif
            //targetPointer = gep->getPointerOperand();
            //hz: get field-sensitive point-to information for this GEP operator and record it in the global status.
            targetPointer = visitGetElementPtrOperator(&I,gep);
        } else {
            if(!hasPointsToObjects(targetPointer)) {
                targetPointer = targetPointer->stripPointerCasts();
#ifdef DEBUG_STORE_INSTR
                dbgs() << "No point-to info for targetPointer, try to strip the pointer casts -0.\n";
                dbgs() << "After strip, the targetPointer is: " << InstructionUtils::getValueStr(targetPointer) << "\n";
#endif
            }
        }
        Value *targetValue = I.getValueOperand();
        gep = dyn_cast<GEPOperator>(targetValue);
        if(gep && gep->getNumOperands() > 0 && gep->getPointerOperand() && !dyn_cast<GetElementPtrInst>(targetValue)) {
#ifdef DEBUG_STORE_INSTR
            dbgs() << "There is a GEP operator for targetValue: " << InstructionUtils::getValueStr(gep) << "\n";
#endif
            //targetValue = gep->getPointerOperand();
            //hz: get field-sensitive point-to information for this GEP operator and record it in the global status.
            targetValue = visitGetElementPtrOperator(&I,gep);
        }
        Value *targetValue_pre_strip = targetValue;
        // handle pointer casts
        if (!hasPointsToObjects(targetValue)) {
            targetValue = targetValue->stripPointerCasts();
#ifdef DEBUG_STORE_INSTR
            dbgs() << "No point-to info for targetValue, try to strip the pointer casts -1.\n";
            dbgs() << "After strip, the targetValue is: " << InstructionUtils::getValueStr(targetValue) << "\n";
#endif
        }
        //Let's not create dummy objs for the targetValue when processing the store inst to avoid the pointee explosion, if the targetValue
        //really deserves a pointee dummy obj it should has already been created by other inst visitors.
        /*
#ifdef CREATE_DUMMY_OBJ_IF_NULL
        //hz: try to create dummy objects if there is no point-to information about the pointer variable,
        //since it can be an outside global variable. (e.g. platform_device).
        if(!hasPointsToObjects(targetValue)) {
#ifdef DEBUG_STORE_INSTR
            dbgs() << "Still no point-to for targetValue, try to create an outside object for: " << InstructionUtils::getValueStr(targetValue_pre_strip) << "\n";
#endif
            if(this->createOutsideObj(targetValue_pre_strip,true)){
#ifdef DEBUG_STORE_INSTR
                dbgs() << "Created successfully.\n";
#endif
                targetValue = targetValue_pre_strip;
            }
        }
#endif
        */
        // Get the src points to information.
        std::set<PointerPointsTo*> *srcPointsTo = getPointsToObjects(targetValue);
        if (!srcPointsTo || srcPointsTo->empty()) {
            //The src to store doesn't point to anything, maybe this is because the src is a scalar instead of a pointer,
            //anyway no need to process this store inst any more since what we are doing is a point-to analysis.
#ifdef DEBUG_STORE_INSTR
            dbgs() << "visitStoreInst(): src does not point to anything: " << InstructionUtils::getValueStr(targetValue) << "; Ignoring.\n";
#endif
            //TODO: can we ignore the timing info since this is an early return?
            return;
        }
        //Get the dst points-to info.
        if(!hasPointsToObjects(targetPointer)) {
            targetPointer = targetPointer->stripPointerCasts();
        }
        std::set<PointerPointsTo *> *dstPointsTo = getPointsToObjects(targetPointer);
        if(dstPointsTo == nullptr || dstPointsTo->empty()) {
#ifdef DEBUG_STORE_INSTR
            dbgs() << "Trying to store something into pointer, which does not point to anything\n";
#endif
#ifdef STRICT_STORE
            assert("Null dstPointsTo set in visitStoreInst()" && false);
#endif
            //TODO: can we ignore the timing info since this is an early return?
            return;
        }
        //NOTE: when processing the store inst we do *not* need to update the pto info for the "targetPointer" - it will
        //always point to the same location(s). What we really need to update is the pto info of the memory location(s) pointed
        //to by the "targetPointer" (i.e. "targetPointer" is a 2nd order pointer).
        int is_weak = dstPointsTo->size() > 1 ? 1 : 0;
        InstLoc *propInst = new InstLoc(&I,this->currFuncCallSites);
        for (PointerPointsTo *currPointsTo: *dstPointsTo) {
            //Basic Sanity
            if(!((currPointsTo->targetPointer == targetPointer || currPointsTo->targetPointer == targetPointer->stripPointerCasts()) &&
                currPointsTo->fieldId == 0)) {
                dbgs() << "We're going to crash in AliasAnalysisVisitor::visitStoreInst() :( ...\n";
                dbgs() << "Inst: " << InstructionUtils::getValueStr(&I) << "\n";
                dbgs() << "currPointsTo->targetPointer: " << InstructionUtils::getValueStr(currPointsTo->targetPointer) << "\n";
                dbgs() << "targetPointer: " << InstructionUtils::getValueStr(targetPointer) << "\n";
                dbgs() << "targetPointer->stripPointerCasts(): " << InstructionUtils::getValueStr(targetPointer->stripPointerCasts()) << "\n";
                dbgs() << (currPointsTo->targetPointer == targetPointer) << " | " << (currPointsTo->targetPointer == targetPointer->stripPointerCasts()) << "\n";
                dbgs() << "currPointsTo->fieldId: " << currPointsTo->fieldId << "\n";
                assert(false);
            }
            // perform update
            currPointsTo->targetObject->updateFieldPointsTo(currPointsTo->dstfieldId, srcPointsTo, propInst, is_weak);
        }
#ifdef TIMING
        dbgs() << "[TIMING] AliasAnalysisVisitor::visitStoreInst(): ";
        InstructionUtils::getTimeDuration(t0,&dbgs());
#endif
    }

    // The following instructions are ignored.
    // we will deal with them, if we find them
    void AliasAnalysisVisitor::visitVAArgInst(VAArgInst &I) {
        assert(false);
    }

    void AliasAnalysisVisitor::visitVACopyInst(VACopyInst &I) {
        assert(false);
    }

    //Propagate the pto records of the actual args to the formal args. 
    void AliasAnalysisVisitor::setupCallContext(CallInst &I, Function *currFunction, std::vector<Instruction *> *newCallContext) {

        std::map<Value *, std::set<PointerPointsTo*>*> *currFuncPointsTo = currState.getPointsToInfo(newCallContext);

        // This ensures that we never analyzed this function with the same context.
        //assert(currFuncPointsTo->size() == 0);

        unsigned int arg_no = 0;

        for(User::op_iterator arg_begin = I.arg_begin(), arg_end = I.arg_end(); arg_begin != arg_end; arg_begin++) {
            Value *currArgVal =(*arg_begin).get();

            if(hasPointsToObjects(currArgVal) || hasPointsToObjects(currArgVal->stripPointerCasts())) {
                unsigned int farg_no;
                farg_no = 0;
                std::set<Value*> valuesToMerge;
                // handle pointer casts
                if(!hasPointsToObjects(currArgVal)) {
                    currArgVal = currArgVal->stripPointerCasts();
                }
                valuesToMerge.clear();
                valuesToMerge.insert(valuesToMerge.end(), currArgVal);

                for(Function::arg_iterator farg_begin = currFunction->arg_begin(), farg_end = currFunction->arg_end();
                        farg_begin != farg_end; farg_begin++) {
                    Value *currfArgVal = &(*farg_begin);
                    if(farg_no == arg_no) {
                        std::set<PointerPointsTo*> *currArgPointsTo = mergePointsTo(valuesToMerge, &I, currfArgVal);
                        // ensure that we didn't mess up.
                        assert(currArgPointsTo != nullptr);
#ifdef DEBUG_CALL_INSTR
                        // OK, we need to add pointsto.
                        dbgs() << "Argument:" << (arg_no + 1) << " has points to information\n";
#endif
                        (*currFuncPointsTo)[currfArgVal] = currArgPointsTo;
                        break;
                    }
                    farg_no++;
                }
            } else {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "Argument:" << (arg_no + 1) << " does not point to any object\n";
#endif
            }
            arg_no++;
        }
    }


    void AliasAnalysisVisitor::handleMemcpyFunction(std::vector<long> &memcpyArgs, CallInst &I) {
        // handle memcpy instruction.
#ifdef DEBUG_CALL_INSTR
        dbgs() << "Processing memcpy function\n";
#endif
        // get src operand
        Value *srcOperand = I.getArgOperand((unsigned int) memcpyArgs[0]);
        // get dst operand
        Value *dstOperand = I.getArgOperand((unsigned int) memcpyArgs[1]);
        // handle pointer casts
        if(!hasPointsToObjects(srcOperand)) {
            srcOperand = srcOperand->stripPointerCasts();
        }
        if(!hasPointsToObjects(dstOperand)) {
            dstOperand = dstOperand->stripPointerCasts();
        }

        // get points to information.
        std::set<PointerPointsTo*>* srcPointsTo = getPointsToObjects(srcOperand);
        std::set<PointerPointsTo*>* dstPointsTo = getPointsToObjects(dstOperand);

        if(srcPointsTo != nullptr && srcPointsTo->size() && dstPointsTo != nullptr && dstPointsTo->size()) {
            // get all src objects.

            std::set<std::pair<long, AliasObject*>> srcAliasObjects;
            for(PointerPointsTo *currPointsTo:(*srcPointsTo)) {
                auto a = std::make_pair(currPointsTo->dstfieldId, currPointsTo->targetObject);
                if(srcAliasObjects.find(a) == srcAliasObjects.end()) {
                    srcAliasObjects.insert(a);
                }
            }

            std::set<std::pair<long, AliasObject*>> srcDrefObjects;
            InstLoc *propInst = new InstLoc(&I,this->currFuncCallSites);
            for(auto a:srcAliasObjects) {
                a.second->fetchPointsToObjects(a.first, srcDrefObjects, propInst);
            }

            std::set<PointerPointsTo*> targetElements;
            for(auto a:srcDrefObjects) {
                PointerPointsTo *newRel = new PointerPointsTo(nullptr, 0, a.second, a.first, new InstLoc(&I,this->currFuncCallSites), false);
                targetElements.insert(newRel);
            }

#ifdef DEBUG_CALL_INSTR
            dbgs() << "Got:" << targetElements.size() << " to add\n";
#endif
            for(auto a:(*dstPointsTo)) {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "Adding:" << targetElements.size() << "elements to the fieldid:" << a->dstfieldId << "\n";
#endif
                //If there are multiple destinations we should perform a weak update, otherwise strong.
                a->targetObject->updateFieldPointsTo(a->dstfieldId, &targetElements, propInst, dstPointsTo->size() > 1 ? 1 : 0);
            }

            for(auto a:targetElements) {
                delete(a);
            }


        } else {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Either src or dst doesn't have any points to information, "
                "ignoring memory copy function in propagating points to information\n";
#endif
        }
    }

    void AliasAnalysisVisitor::handleFdCreationFunction(std::map<long,long> &fdFieldMap, Function *currFunc, CallInst &I) {
        if (!currFunc) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::handleFdCreationFunction(): Null currFunc!!!\n";
#endif
            return;
        }
        //We need to create a new struct.file object and set its field point-to according to the field-to-arg map.
        std::string fn("struct.file");
        Type *file_ty = InstructionUtils::getStTypeByName(I.getModule(), fn);
        if (!file_ty) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::handleFdCreationFunction(): Cannot get the struct.file type!!!\n";
#endif
        }
        //If we have already visited this call site then the file obj should already be created, now let's just skip it.
        //NOTE: count == 1 means that it's the first time we're analyzing current BB, among all call contexts.
        if ( this->currState.numTimeAnalyzed.find(I.getParent()) != this->currState.numTimeAnalyzed.end() &&
             this->currState.numTimeAnalyzed[I.getParent()] > 1 ) {
            //TODO: "anon_inode_getfd" doesn't return the pointer to the created file struct, so we don't need to update the point-to of this call inst,
            //but we may have other fd creation functions that needs us to do so. If that's the case, we need to retrieve the previously created obj and update the pointer.
            return;
        }
        //Type based object creation.
        //Since this will create a fd, we always treat it as a global taint source.
        InstLoc *propInst = new InstLoc(&I,this->currFuncCallSites);
        std::set<TaintFlag*> existingTaints;
        TaintTag *tag = new TaintTag(0,file_ty,true);
        TaintFlag *tf = new TaintFlag(propInst,true,tag);
        existingTaints.insert(tf);
        OutsideObject *newObj = DRCHECKER::createOutsideObj(file_ty,true,&existingTaints);
        //Ok, now add it to the global object cache.
        if (newObj) {
            //Update the field point-to according to the "fdFieldMap".
            for (auto &e : fdFieldMap) {
                long fid = e.first;
                long arg_no = e.second;
                if (arg_no == -1) {
                    //this means the function return value should point to the newly created file struct.
                    std::set<PointerPointsTo*> *newPointsToInfo = new std::set<PointerPointsTo*>();
                    PointerPointsTo *pto = new PointerPointsTo(&I, 0, newObj, 0, propInst, false);
                    newPointsToInfo->insert(pto);
                    this->updatePointsToObjects(&I, newPointsToInfo);
                    continue;
                }
                if (arg_no < 0 || arg_no >= (long)I.getNumArgOperands()) {
                    continue;
                }
                Value *arg = I.getArgOperand(arg_no);
                if (arg && hasPointsToObjects(arg)) {
                    std::set<PointerPointsTo*>* srcPointsTo = getPointsToObjects(arg);
                    //We're sure that the "newObj" field pto will be updated, so it's a strong update.
                    newObj->updateFieldPointsTo(fid,srcPointsTo,propInst,0);
                }
            }
            DRCHECKER::addToSharedObjCache(newObj);
        }else {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "AliasAnalysisVisitor::handleFdCreationFunction(): Cannot create the file struct!!!\n";
#endif
        }
    }

    VisitorCallback* AliasAnalysisVisitor::visitCallInst(CallInst &I, Function *currFunc,
            std::vector<Instruction *> *oldFuncCallSites,
            std::vector<Instruction *> *callSiteContext) {

#ifdef DEBUG_CALL_INSTR
        dbgs() << "AliasAnalysisVisitor::visitCallInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        std::string currFuncName = currFunc->getName().str();
        // if we do not have function definition
        // that means, it is a kernel internal function.
        // call kernel intra-function handler.
        if(currFunc->isDeclaration()) {
            FunctionChecker *targetChecker = (AliasAnalysisVisitor::functionHandler)->targetChecker;
            if(targetChecker->is_memcpy_function(currFunc)) {
                // handle memcpy function.
                std::vector<long> memcpyArgs = targetChecker->get_memcpy_arguments(currFunc);
                this->handleMemcpyFunction(memcpyArgs, I);
            }else if (targetChecker->is_fd_creation_function(currFunc)) {
                // handle fd creation function
                std::map<long,long> fdFieldMap = targetChecker->get_fd_field_arg_map(currFunc);
                this->handleFdCreationFunction(fdFieldMap,currFunc,I);
            }else {
                //std::set<PointerPointsTo*>* newPointsToInfo = KernelFunctionHandler::handleKernelFunction(I, currFunc, this->currFuncCallSites);
                bool is_handled;
                is_handled = false;
                std::set<PointerPointsTo *> *newPointsToInfo = (std::set<PointerPointsTo *> *) ((AliasAnalysisVisitor::functionHandler)->handleFunction(
                            I, currFunc,
                            (void *) (this->currFuncCallSites),
                            AliasAnalysisVisitor::callback,
                            is_handled));
                if (is_handled) {
#ifdef DEBUG_CALL_INSTR
                    dbgs() << "Function:" << currFuncName << " handled by the function handler\n";
#endif
                    if (newPointsToInfo != nullptr) {
#ifdef DEBUG_CALL_INSTR
                        dbgs() << "Function handler returned some points to info to add\n";
#endif
                        this->updatePointsToObjects(&I, newPointsToInfo);
                    }
                } else {
#ifdef DEBUG_CALL_INSTR
                    dbgs() << "Ignoring Kernel Function:" << currFuncName << "\n";
#endif
                }
            }
            return nullptr;
        }

        // Setup call context.
        setupCallContext(I, currFunc, callSiteContext);

        // Create a AliasAnalysisVisitor
        AliasAnalysisVisitor *vis = new AliasAnalysisVisitor(currState, currFunc, callSiteContext);

        return vis;
    }

    void AliasAnalysisVisitor::stitchChildContext(CallInst &I, VisitorCallback *childCallback) {
        AliasAnalysisVisitor *vis = (AliasAnalysisVisitor *)childCallback;
        if(vis->retValPointsTo.size() > 0 ){
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Stitching return value for call instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
            std::set<PointerPointsTo*>* newPointsToInfo = this->copyPointsToInfo(&I, &(vis->retValPointsTo));
            if(newPointsToInfo != nullptr) {
                this->updatePointsToObjects(&I, newPointsToInfo);
            }
        }

    }

    void AliasAnalysisVisitor::visitReturnInst(ReturnInst &I) {
        Value *targetRetVal = I.getReturnValue();
        if(targetRetVal != nullptr && (hasPointsToObjects(targetRetVal) || hasPointsToObjects(targetRetVal->stripPointerCasts()))) {
            // check if pointer casts has a role to play?
            if(!hasPointsToObjects(targetRetVal)){
                targetRetVal = targetRetVal->stripPointerCasts();
            }
            std::set<PointerPointsTo*>* srcPointsTo = getPointsToObjects(targetRetVal);
            // Get all objects pointed by all the objects in the targetRetVal

            // this set stores the <fieldid, targetobject> of all the objects to which the targetRetVal points to.
            std::set<std::pair<long, AliasObject*>> targetObjects;
            for(PointerPointsTo *currPointsToObj:*srcPointsTo) {
                if(std::find_if(retValPointsTo.begin(), retValPointsTo.end(), [currPointsToObj](const PointerPointsTo *n) {
                            return  n->pointsToSameObject(currPointsToObj);
                            }) == retValPointsTo.end()) {
                    long target_field = currPointsToObj->dstfieldId;
                    AliasObject *dstObj = currPointsToObj->targetObject;
                    auto to_check = std::make_pair(target_field, dstObj);
                    if (std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                        targetObjects.insert(targetObjects.end(), to_check);
                        // insert into retval points to
#ifdef DEBUG_RET_INSTR
                        dbgs() << "Return value:";
                        I.print(dbgs());
                        dbgs() << ", points to some objects\n";
#endif
                        retValPointsTo.insert(retValPointsTo.end(), currPointsToObj);
                    }
                }
            }
        } else {
#ifdef DEBUG_RET_INSTR
            dbgs() << "Return value:";
            I.print(dbgs());
            dbgs() << ", does not point to any object. Ignoring.\n";
#endif
        }
    }

    void AliasAnalysisVisitor::printAliasAnalysisResults(llvm::raw_ostream& O) const {
        /***
         * Dump all the alias analysis result information into provided stream.
         */
        std::map<Value *, std::set<PointerPointsTo*>*>* targetPointsToMap = this->currState.getPointsToInfo(this->currFuncCallSites);
        for(auto ai:*targetPointsToMap) {
            O << "\nPointer:";
            ai.first->print(O);
            O << " has following points to information:\n";
            for(auto pp:*(ai.second)) {
                O << (*pp);
                O << "\n";
            }
        }
    }
}
