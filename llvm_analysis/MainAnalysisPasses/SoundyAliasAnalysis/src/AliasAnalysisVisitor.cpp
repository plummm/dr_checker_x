//
// Created by machiry on 12/4/16.
//
#include "AliasAnalysisVisitor.h"

namespace DRCHECKER {

#define DEBUG_GET_ELEMENT_PTR
//#define DEBUG_ALLOCA_INSTR
//#define DEBUG_CAST_INSTR
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
//#define DEBUG_TMP

    //hz: A helper method to create and (taint) a new OutsideObject.
    OutsideObject* AliasAnalysisVisitor::createOutsideObj(Value *p, bool taint) {
        std::map<Value *, std::set<PointerPointsTo*>*> *currPointsTo = this->currState.getPointsToInfo(this->currFuncCallSites);
        std::set<TaintFlag*> *existingTaints = nullptr;
        //Need to taint it?
        if (taint) {
            existingTaints = TaintUtils::getTaintInfo(this->currState,this->currFuncCallSites,p);
        }
        return DRCHECKER::createOutsideObj(p, currPointsTo, taint, existingTaints);
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
                // for each points to, see if we already have that information, if yes, ignore it.
                if(std::find_if(existingPointsTo->begin(), existingPointsTo->end(), [currPointsTo,dbg](const PointerPointsTo *n) {
                    //hz: a simple hack here to avoid duplicated objects.
                    if(dbg){
                        dbgs() << "----------------------------\n";
                    }
                    if(currPointsTo->dstfieldId != n->dstfieldId){
                        if(dbg){
                            dbgs() << "dstField mismatch: " << n->dstfieldId << "\n";
                        }
                        return false;
                    }
                    AliasObject *o0 = currPointsTo->targetObject;
                    AliasObject *o1 = n->targetObject;
                    if(dbg){
                        dbgs() << (o0?"t":"f") << (o1?"t":"f") << (o0?(o0->isOutsideObject()?"t":"f"):"n") << (o1?(o1->isOutsideObject()?"t":"f"):"n") << "\n";
                    }
                    if(o0 && o1){
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
                            dbgs() << "Ptr0: " << InstructionUtils::getValueStr(v0) << " Ptr1: " << InstructionUtils::getValueStr(v1) << "RES: " << (v0==v1?"T":"F") << "\n";
                        }
                        if(v0 || v1){
                            return (v0 == v1);
                        }
                    }else if(o0 || o1){
                        //One is null but the other is not, obviously not the same.
                        if(dbg){
                            dbgs() << "One of the 2 objs is null\n";
                        }
                        return false;
                    }
                    if(dbg){
                        dbgs() << "Default Cmp\n";;
                    }
                    return  n->isIdenticalPointsTo(currPointsTo);
                }) == existingPointsTo->end()) {
                    if(dbg){
                        dbgs() << "############# Inserted!!!\n";
                    }
#ifdef DEBUG_UPDATE_POINTSTO
                    dbgs() << "Insert point-to: " << InstructionUtils::getTypeStr(currPointsTo->targetObject->targetType);
                    dbgs() << " | " << currPointsTo->dstfieldId << " ,is_taint_src: " << currPointsTo->targetObject->is_taint_src << "\n";
                    dbgs() << "Obj ID: " << (const void*)(currPointsTo->targetObject) << "\n";
                    Value *tv = currPointsTo->targetObject->getValue();
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
               targetPointsToMap->find(srcPointer) != targetPointsToMap->end();
    }

    //In this version, we assume that "srcPointsTo" points to an embedded struct in a host struct.
    //NOTE: "srcPointer" in this function is related to "srcPointsTo".
    std::set<PointerPointsTo*>* AliasAnalysisVisitor::makePointsToCopy_emb(Instruction *propInstruction, Value *srcPointer, Value *resPointer,
                                                             std::set<PointerPointsTo*>* srcPointsTo, long fieldId) {
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): elements in *srcPointsTo: " << srcPointsTo->size() << " \n";
#endif
        std::set<PointerPointsTo*>* newPointsToInfo = new std::set<PointerPointsTo*>();
        for(PointerPointsTo *currPointsToObj : *srcPointsTo) {
            AliasObject *hostObj = currPointsToObj->targetObject;
            if (!hostObj) {
                continue;
            }
            long dstField = currPointsToObj->dstfieldId;
            //We must ensure that it points to an embedded struct in another struct.
            Type *host_type = hostObj->targetType;
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "--- ";
            if (host_type) {
                dbgs() << "host_type: " << InstructionUtils::getTypeStr(host_type) << " | " << dstField;
            }
            dbgs() << "\n";
#endif
            if (!host_type || !host_type->isStructTy() || host_type->getStructNumElements() <= dstField || dstField < 0) {
                continue;
            }
            Type *hostSubTy = host_type->getStructElementType(dstField);
            if (!hostSubTy) {
                continue;
            }
            Type *hostArrSubTy = nullptr;
            if (hostSubTy->isArrayTy()){
                hostArrSubTy = hostSubTy->getArrayElementType();
            }
            PointerPointsTo *newPointsToObj = new PointerPointsTo();
            newPointsToObj->propogatingInstruction = propInstruction;
            newPointsToObj->fieldId = 0;
            if (hostObj->from_array && dstField == 0 && fieldId < host_type->getStructNumElements()) {
                //This means current pointee obj is from an array, so the last GEP index was used to locate it in the array (instead of locating an embed struct in the host struct),
                //so current field ID will directly index into "hostObj" (instead of the embed struct located in field 0 of "hostObj").
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): current pointee obj is from an array..\n";
#endif
                //TODO: is this right??
                hostObj->from_array = false;
                newPointsToObj->targetPointer = resPointer;
                if (fieldId >= 0) {
                    newPointsToObj->dstfieldId = fieldId;
                }else {
                    newPointsToObj->dstfieldId = 0;
                }
                newPointsToObj->targetObject = hostObj;
                newPointsToInfo->insert(newPointsToInfo->begin(), newPointsToObj);
            }else if (hostSubTy->isStructTy() && fieldId < hostSubTy->getStructNumElements()) {
                //Ok, it's an emb struct, create new emb struct if necessary.
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): current pointee obj is an embedded struct..\n";
#endif
                newPointsToObj->targetPointer = resPointer;
                AliasObject *newObj = this->createEmbObj(hostObj,dstField,srcPointer);
                if(newObj){
                    newPointsToObj->targetObject = newObj;
                    if(fieldId >= 0){
                        newPointsToObj->dstfieldId = fieldId;
                    }else{
                        //Is this possible??
                        newPointsToObj->dstfieldId = 0;
                    }
                    newPointsToInfo->insert(newPointsToInfo->begin(), newPointsToObj);
                }else{
#ifdef DEBUG_GET_ELEMENT_PTR
                    errs() << "In AliasAnalysisVisitor::makePointsToCopy_emb(): cannot get or create embedded object.\n";
#endif
                    delete(newPointsToObj);
                }
            }else if (hostArrSubTy && fieldId < hostSubTy->getArrayNumElements()) {
                //It's an embedded array, the result pointer should point to one array element.
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): current pointee obj is an embedded array..\n";
#endif
                newPointsToObj->targetPointer = resPointer;
                newPointsToObj->dstfieldId = 0;
                AliasObject *newObj = this->createEmbObj(hostObj,dstField,resPointer);
                if(newObj){
                    newObj->from_array = true;
                    newPointsToObj->targetObject = newObj;
                    newPointsToInfo->insert(newPointsToInfo->begin(), newPointsToObj);
                }else {
#ifdef DEBUG_GET_ELEMENT_PTR
                    errs() << "In AliasAnalysisVisitor::makePointsToCopy_emb(): cannot get or create embedded object.\n";
#endif
                    delete(newPointsToObj);
                }
            }
        }
        return newPointsToInfo;
    }

    AliasObject *AliasAnalysisVisitor::createEmbObj(AliasObject *hostObj, long host_dstFieldId, Value *v) {
        std::map<Value *, std::set<PointerPointsTo*>*> *currPointsTo = this->currState.getPointsToInfo(this->currFuncCallSites);
        return DRCHECKER::createEmbObj(hostObj, host_dstFieldId, v, currPointsTo);
    }

    std::set<PointerPointsTo*>* AliasAnalysisVisitor::makePointsToCopy(Instruction *propInstruction, Value *srcPointer,
            std::set<PointerPointsTo*>* srcPointsTo, long fieldId) {
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
        for(PointerPointsTo *currPointsToObj:*srcPointsTo) {
            AliasObject *hostObj = currPointsToObj->targetObject;
            // if the target object is not visited, then add into points to info.
            if(hostObj && visitedObjects.find(hostObj) == visitedObjects.end()) {
                PointerPointsTo *newPointsToObj = new PointerPointsTo();
                newPointsToObj->propogatingInstruction = propInstruction;
                //hz: 'dstField' is a complex issue, we first apply original logic to set the default "dstfieldId", then
                //make some modifications if possible:
                //(1) if src pointer points to a non-struct field in the src object, we can try to update "dstField" with the arg "fieldId".
                //(2) if src points to an embedded struct field in the src object, then the arg "fieldId" indexes into the embedded struct
                //instead of the src object... We need special handling here.
                //----------ORIGINAL-----------
                if(fieldId >= 0) {
                    newPointsToObj->dstfieldId = fieldId;
                } else {
                    newPointsToObj->dstfieldId = currPointsToObj->dstfieldId;
                }
                newPointsToObj->fieldId = 0;
                newPointsToObj->targetObject = hostObj;
                newPointsToObj->targetPointer = srcPointer;
                //----------ORIGINAL-----------
                //----------MOD----------
                bool is_emb = false;
                long host_dstFieldId = currPointsToObj->dstfieldId;
                //The arg "srcPointer" actually is not related to arg "srcPointsTo", it's indeed "dstPointer" that we need to copy point-to inf for.
                GEPOperator *gep = (srcPointer ? dyn_cast<GEPOperator>(srcPointer) : nullptr);
                //"basePointerType" refers to the type of the pointer operand in the original GEP instruction/opearator, during whose visit we
                //call this makePointsToCopy().
                Type *basePointerType = (gep ? gep->getPointerOperand()->getType() : nullptr);
                Type *basePointToType = (basePointerType ? basePointerType->getPointerElementType() : nullptr);
                //Get type information about current point-to object.
                Type *host_type = hostObj->targetType;
                if (!host_type){
                    //TODO: It's unlikely, but is this skip safe?
                    goto fail_next;
                }
                if(host_type->isPointerTy()){
                    host_type = host_type->getPointerElementType();
                }
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): basePointerType: " << InstructionUtils::getTypeStr(basePointerType) << "\n";
                dbgs() << "Cur Points-to, host_type: " << InstructionUtils::getTypeStr(host_type) << " | " << host_dstFieldId << "\n";
                dbgs() << "hostObj: " << (const void*)hostObj << "\n";
#endif
                //hz: the following several "if" try to decide whether we will actually index into an embedded struct in the host struct.
                //NOTE: fieldId < 0 means that we simply want to copy the points-to information w/o changing anything.
                if (basePointToType && basePointToType->isStructTy() && host_type->isStructTy() &&
                        host_type->getStructNumElements() > host_dstFieldId && !InstructionUtils::same_types(host_type,basePointToType) && fieldId >= 0)
                {
                    Type *src_fieldTy = host_type->getStructElementType(host_dstFieldId);
                    //It's also possible that the field is an array of a certain struct, if so, we should also regard this field as
                    //a "struct" field (i.e. the first struct in the array).
                    Type *src_fieldTy_arrElem = nullptr;
                    if(src_fieldTy && src_fieldTy->isArrayTy()){
                        src_fieldTy_arrElem = src_fieldTy->getArrayElementType();
                    }
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "src_fieldTy: " << InstructionUtils::getTypeStr(src_fieldTy) << "\n";
                    dbgs() << "src_fieldTy_arrElem: " << InstructionUtils::getTypeStr(src_fieldTy_arrElem) << "\n";
#endif
                    if( (src_fieldTy && src_fieldTy == basePointToType) ||
                            (src_fieldTy_arrElem && src_fieldTy_arrElem == basePointToType)
                      )
                    {
                        is_emb = true;
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): index into an embedded struct in the host object!\n";
#endif
                        //Ok, the src points to a struct embedded in the host object, we cannot just use
                        //the arg "fieldId" as "dstfieldId" of the host object because it's an offset into the embedded struct.
                        //We have two candidate methods here:
                        //(1) Create a separate TargetObject representing this embedded struct, then make the pointer operand in original GEP point to it.
                        //(2) Directly create an outside object for the resulted pointer of this GEP. (i.e. the parameter "srcPointer")
                        //Method (1):
                        AliasObject *newObj = this->createEmbObj(hostObj,host_dstFieldId,gep->getPointerOperand());
                        if(newObj){
                            newPointsToObj->targetObject = newObj;
                            if(fieldId >= 0){
                                newPointsToObj->dstfieldId = fieldId;
                            }else{
                                //Is this possible??
                                newPointsToObj->dstfieldId = 0;
                            }
                        }else{
                            //We cannot create the new OutsideObject, it's possibly because the target pointer doesn't point to a struct.
                            //In this case, rather than using the original wrong logic, we'd better make it point to nothing.
#ifdef DEBUG_GET_ELEMENT_PTR
                            errs() << "In makePointsToCopy(): cannot get or create embedded object for: " << InstructionUtils::getValueStr(gep->getPointerOperand()) << "\n";
#endif
                            goto fail_next;
                        }
                        /*
                        //Method (2):
                        OutsideObject *newObj = this->createOutsideObj(srcPointer,false);
                        if(newObj){
                            newObj->is_taint_src = hostObj-->is_taint_src;
                            //This new TargetObject should also be tainted according to the host object taint flags.
                            std::set<TaintFlag*> *src_taintFlags =  hostObj->getFieldTaintInfo(host_dstFieldId);
                            if(src_taintFlags){
                                for(TaintFlag *currTaintFlag:*src_taintFlags){
                                    newObj->taintAllFieldsWithTag(currTaintFlag);
                                }
                            }
                            newPointsToObj->targetObject = newObj;
                            //Since now the newObj directly represents the final resulted object of this GEP (instead of the embedded struct),
                            //we will set the dstField to 0.
                            newPointsToObj->dstfieldId = 0;
                        }else{
                            //We cannot create the new OutsideObject, it's possibly because the target pointer doesn't point to a struct.
                            //In this case, rather than using the original wrong logic, we'd better make it point to nothing.
#ifdef DEBUG_GET_ELEMENT_PTR
                            errs() << "In makePointsToCopy(): cannot create OutsideObject for: ";
                            srcPointer->print(errs());
                            errs() << "\n";
#endif
                            goto fail_next;
                        }
                         */
                    }
                }
                //----------MOD----------
                if (newPointsToObj){
                    //Insert the points-to info in two cases:
                    //(1) It indexes into an embedded structure (that we have already properly handled)
                    //(2) It's not an embedded structure, and the target field ID doesn't exceed the host structure's limit.
                    if (is_emb || fieldId <= 0 || (!host_type->isStructTy()) || host_type->getStructNumElements() > fieldId){
                        newPointsToInfo->insert(newPointsToInfo->begin(), newPointsToObj);
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "Assign points-to object: ";
                        if(newPointsToObj->targetObject){
                            dbgs() << InstructionUtils::getTypeStr(newPointsToObj->targetObject->targetType);
                        }
                        dbgs() << " | dstField: " << newPointsToObj->dstfieldId << "\n";

#endif
                    }
                }
                visitedObjects.insert(visitedObjects.begin(), hostObj);
                continue;
fail_next:
                delete newPointsToObj;
                visitedObjects.insert(visitedObjects.begin(), hostObj);
                continue;
        }//if in visitedObjects
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
    if(targetObjects.size() > 0) {
        std::set<PointerPointsTo*>* toRetPointsTo = new std::set<PointerPointsTo*>();
        for(auto currItem: targetObjects) {
            PointerPointsTo* currPointsToObj = new PointerPointsTo();
            currPointsToObj->targetPointer = targetInstruction;
            if(targetPtr != nullptr) {
                currPointsToObj->targetPointer = targetPtr;
            }
            currPointsToObj->targetObject = currItem.second;
            currPointsToObj->dstfieldId = currItem.first;
            currPointsToObj->fieldId = 0;
            currPointsToObj->propogatingInstruction = targetInstruction;
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
            PointerPointsTo* currPointsToObj = new PointerPointsTo();
            currPointsToObj->targetPointer = srcInstruction;
            currPointsToObj->targetObject = currItem.second;
            currPointsToObj->dstfieldId = currItem.first;
            currPointsToObj->fieldId = 0;
            currPointsToObj->propogatingInstruction = srcInstruction;
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
        dbgs() << "The Alloca instruction, already processed:";
        I.print(dbgs());
        dbgs() << "\n";
#endif
        return;
    }
    AliasObject *targetObj = new FunctionLocalVariable(I, this->currFuncCallSites);
    PointerPointsTo *newPointsTo = new PointerPointsTo();
    newPointsTo->fieldId = 0;
    newPointsTo->dstfieldId = 0;
    newPointsTo->propogatingInstruction = &I;
    newPointsTo->targetObject = targetObj;
    newPointsTo->targetPointer = &I;
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
            //NOTE: the "targetObject" will not be copied.
            PointerPointsTo *newPointsToObj = (PointerPointsTo*)currPointsToObj->makeCopy();
            newPointsToObj->propogatingInstruction = &I;
            newPointsToObj->targetPointer = &I;
            //TODO: this may be unnecessary since the "targetObject" will not be copied.
            newPointsToObj->targetObject->is_taint_src = currPointsToObj->targetObject->is_taint_src;
            Type *currTgtObjType = newPointsToObj->targetObject->targetType;
#ifdef DEBUG_CAST_INSTR
            dbgs() << "AliasAnalysisVisitor::visitCastInst: current target object: " << InstructionUtils::getTypeStr(currTgtObjType) << " | " << currPointsToObj->dstfieldId << "\n";
#endif
            //--------below are special processings for the point-to information---------
            if(!dstType->isVoidTy()) {
                //src type is i8* || i8
                if((currTgtObjType->isPointerTy() && currTgtObjType->getContainedType(0)->isIntegerTy(8)) || currTgtObjType->isIntegerTy(8)){
                    // No need to make copy
                    if(dstType->isPointerTy()) {
                        dstType = dstType->getContainedType(0);
                    }
                    newPointsToObj->targetObject->targetType = dstType;
                    //We also need to re-taint the object (if necessary) since its type has changed.
                    std::set<TaintFlag*> *fieldTaint = newPointsToObj->targetObject->getFieldTaintInfo(0);
                    if (fieldTaint) {
                        for (TaintFlag *tf : *fieldTaint) {
                            newPointsToObj->targetObject->taintAllFieldsWithTag(tf);
                        }
                    }
                }else if (srcPointeeTy && srcPointeeTy->isStructTy() && dstPointeeTy && dstPointeeTy->isStructTy() &&
                          currTgtObjType == srcPointeeTy && newPointsToObj->dstfieldId == 0){
                    //TODO: what if the pointee is an embedded struct (dstfieldId != 0) in the host obj...
                    //hz: what if src pointer is not i8*?
                    //hz: we need make a copy of original targetObject and change its type to dstType,
                    //hz: we also need to properly handle the taint information.
#ifdef DEBUG_CAST_INSTR
                    dbgs() << "About to copy src object to dst object of a different type.\n";
#endif
                    AliasObject *newTargetObj = this->x_type_obj_copy(newPointsToObj->targetObject,dstPointeeTy);
                    if (newTargetObj){
                        newPointsToObj->targetObject = newTargetObj;
                    }else{
                        //TODO: what to do now..
#ifdef DEBUG_CAST_INSTR
                        dbgs() << "x_type_obj_copy failed..\n";
#endif
                    }
                }
            }else{
                //TODO: hz: what if dst pointer is void?
#ifdef DEBUG_CAST_INSTR
                dbgs() << "dstType is void...\n";
#endif
            }
            //--------above are special processings for the point-to information---------
            newPointsToInfo->insert(newPointsToInfo->end(), newPointsToObj);
        }
        // Update the points to Info of the current instruction.
        this->updatePointsToObjects(&I, newPointsToInfo);
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
    }

    void AliasAnalysisVisitor::processMultiDimensionGEP(Instruction *propInst, GEPOperator *I, std::set<PointerPointsTo*> *srcPointsTo) {
        assert(I);
        if (!I || !srcPointsTo || srcPointsTo->empty()) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processMultiDimensionGEP(): !I || !srcPointsTo || srcPointsTo->empty()\n";
#endif
            return;
        }
        std::set<PointerPointsTo*> *currPointsTo = srcPointsTo;
        bool update = true;
        //We process every index (but still ignore the 1st one) in the GEP, instead of the only 2nd one in the original Dr.Checker.
        for (int i=2; i<I->getNumOperands(); ++i) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "About to process index: " << (i-1) << "\n";
#endif
            ConstantInt *CI = dyn_cast<ConstantInt>(I->getOperand(i));
            if (!CI) {
                //TODO: non-constant index.
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "Non-constant index: " << i << "\n";
#endif
                if (i == 2) {
                    update = false;
                }
                break;
            }
            unsigned long structFieldId = CI->getZExtValue();
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "Index value: " << structFieldId << "\n";
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
                    newPointsToInfo = makePointsToCopy_emb(propInst, subGEP, resGEP, currPointsTo, structFieldId);
                }
            }else {
                //Most GEP should only have 2 indices..
                newPointsToInfo = makePointsToCopy(propInst, I, currPointsTo, structFieldId);
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
        if(update && currPointsTo && !currPointsTo->empty()){
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processMultiDimensionGEP(): updating the point-to for current GEP...\n";
#endif
            //make sure the points-to information includes the correct TargetPointer, which is current GEP inst.
            //TODO: is this ok? Since the pointsTo->targetPointer may not be the "I", it may be a GEP with a subset of indices created by us.
            for (PointerPointsTo *pointsTo : *currPointsTo) {
                pointsTo->targetPointer = I;
            }
            this->updatePointsToObjects(I, currPointsTo);
        }
    }

    //Analyze the 1st dimension of the GEP and return a point-to set of the 1st dimension.
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
            np->propogatingInstruction = propInst;
            np->targetPointer = I;
            srcPointsTo->insert(np);
        }
        //Get the original pointer operand used in this GEP and its type info.
        Value *orgPointer = I->getPointerOperand();
        if (!orgPointer) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): Null orgPointer..return\n";
#endif
            return srcPointsTo;
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
            return srcPointsTo;
        }
        long index = CI->getSExtValue();
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension():: basePointeeTy: " << InstructionUtils::getTypeStr(basePointeeTy) << " 0st index: " << index << "\n";
#endif
        //If the index is zero then 0st dimension will change nothing.
        //Note that this index can be negative.
        if (index == 0) {
            return srcPointsTo;
        }
        //Ok, basically we want to deal w/ a special case here:
        //the pointer operand points to some structs, but the "basePointerTy" of this GEP is an integer pointer (e.g. i8*),
        //this means the struct pointer has been converted to the integer pointer and the struct fields will be accessed in the byte-style...
        //In this situation, we need to calculate which field will actually be pointed-to by the 1st GEP dimention.
        //If this is not the case (e.g. the "basePointerTy" is a normal struct pointer), for now we will just ignore the 1st dimention just as the original Dr.Checker does.
        std::set<PointerPointsTo*> *resPointsTo = new std::set<PointerPointsTo*>();
        if (basePointeeTy && dyn_cast<IntegerType>(basePointeeTy)) {
            IntegerType *int_ty = dyn_cast<IntegerType>(basePointeeTy);
            unsigned width = int_ty->getBitWidth();
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): basePointeeTy is i" << width <<"\n";
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
                //By default it will the same as the original point-to since we will ignore 1st dimension in most cases.
                PointerPointsTo *newPto = new PointerPointsTo();
                newPto->propogatingInstruction = propInst;
                newPto->fieldId = 0;
                newPto->targetPointer = I;
                newPto->targetObject = currPto->targetObject;
                newPto->dstfieldId = currPto->dstfieldId;
                resPointsTo->insert(newPto);
                //Now we will process the special cases where the integer pointer points to a struct...
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): invoke bit2Field()...\n";
#endif
                this->bit2Field(I,newPto,width,index);
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
    void AliasAnalysisVisitor::bit2Field(GEPOperator *I, PointerPointsTo *pto, unsigned bitWidth, long index) {
        static unsigned long suff = 0;
        DataLayout *dl = this->currState.targetDataLayout;
        if (!dl || !pto) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): !dl || !pto\n";
#endif
            return;
        }
        AliasObject *targetObj = pto->targetObject;
        long dstfield = pto->dstfieldId;
        Type *targetObjTy = targetObj->targetType;
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::bit2Field(): host obj: " << InstructionUtils::getTypeStr(targetObjTy) << " | " << dstfield << " obj ID: " << (const void*)targetObj << "\n";
#endif
        if (!targetObjTy || !targetObjTy->isStructTy()) {
            return;
        }
        StructType *stTy = dyn_cast<StructType>(targetObjTy);
        unsigned ne = stTy->getNumElements();
        if (dstfield < 0 || dstfield >= ne) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): dstfield out-of-bound.\n";
#endif
            return;
        }
        //NOTE: StructLayout describes the offset/size of each field in a struct, including the possible padding.
        const StructLayout *stLayout = dl->getStructLayout(stTy);
        if (!stLayout) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): !stLayout\n";
#endif
            return;
        }
        //NOTE: both "dstOffset" and "bits" can be divided by 8, "bits" can be negative.
        long dstOffset = stLayout->getElementOffsetInBits(dstfield);
        long bits = index * (long)bitWidth;
        long resOffset = dstOffset + bits;
        if (resOffset < 0 || resOffset >= stLayout->getSizeInBits()) {
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): resOffset (in bits) out-of-bound.\n";
#endif
            return;
        }
        unsigned resIndex = stLayout->getElementContainingOffset(resOffset/8);
        pto->dstfieldId = resIndex;

        long delta = resOffset - (long)(stLayout->getElementOffsetInBits(resIndex));
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::bit2Field(): dstOffset: " << dstOffset << " bits: " << bits << " resOffset: " << resOffset << " resIndex: " << resIndex << " delta: " << delta << "\n";
#endif
        if (!delta) {
            //An exact match, just update the "pto" to the target field (already done) and return.
            return;
        } else if (delta > 0) {
            //Ok, we have possibly stepped into an embedded object (struct or array/vector).
            //If it's an embedded struct, we need to recursively retrieve/create it and then position the "pto".
            Type *ety = stTy->getElementType(resIndex);
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::bit2Field(): ety: " << InstructionUtils::getTypeStr(ety) << "\n";
#endif
            if (!ety) {
                return;
            }
            if (ety->isStructTy() && I) {
                //First get/create the embedded struct..
                //To invoke createEmbObj() we need a Value that is a pointer to the emb struct, to obtain this pointer, we can:
                //Method 0:
                //(1) First create a cast instruction that convert integer *srcPointer in the "I" to stTy*.
                //(2) Then create a GEP inst that obtains the pointer to the emb obj.
                //Method 1 (in use):
                //Directly create a cast inst to convert srcPointer to ety*.
                Value *orgPointer = I->getPointerOperand();
                ConstantInt *CI = dyn_cast<ConstantInt>(I->getOperand(1));
                if (!orgPointer || !CI) {
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::bit2Field(): !orgPointer || !CI\n";
#endif
                    return;
                }
                //BitCastInst *castInst = new BitCastInst(orgPointer, PointerType::get(stTy, orgPointer->getType()->getPointerAddressSpace()));
                BitCastInst *castInst = new BitCastInst(orgPointer, PointerType::get(ety, orgPointer->getType()->getPointerAddressSpace()), "tmp_cast_" + std::to_string(suff++));
                if (!castInst) {
                    return;
                }
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "BitCastInst: " << InstructionUtils::getValueStr(castInst) << " | ty: " << InstructionUtils::getTypeStr(castInst->getType()) << "\n";
#endif
                /*
                //NOTE: we should give a name to the newly created GEP so that it can pass the sanity check in createOutsideObj().
                std::vector<Value*> indices;
                //0st dimension - keep it to 0.
                indices.push_back(ConstantInt::get(CI->getType(),0));
                //1st dimension - set it to the index of the emb struct.
                indices.push_back(ConstantInt::get(CI->getType(),resIndex));
                ArrayRef<Value*> IdxList(indices);
                GetElementPtrInst *gepInst = GetElementPtrInst::Create(stTy, castInst, IdxList, "tmp_gep_" + std::to_string(suff++));
                if (!gepInst) {
                    return;
                }
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "GEPInst: " << InstructionUtils::getValueStr(gepInst) << " | ty: " << InstructionUtils::getTypeStr(gepInst->getType()) << "\n";
#endif
                */
                AliasObject *newObj = this->createEmbObj(targetObj, resIndex, castInst);
                if (!newObj) {
                    //TODO: what to do now...
                    pto->dstfieldId = 0;
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::bit2Field(): fail to get/create the embedded struct!\n";
#endif
                    //delete(gepInst);
                    delete(castInst);
                    return;
                }
                //Recursively update the "pto".
                pto->targetObject = newObj;
                pto->dstfieldId = 0;
                //TODO: we *might* need to create a different "popInst" here w/ its pointer operand pointing to the embedded struct,
                //but since our current logic will force convert the pointer operand to the target struct type * at first, it should be ok.
                this->bit2Field(I, pto, 8, delta/8);
            } else {
                //TODO: need to do anything for array/vector?
            }
        } else {
            //This should be impossible...
            assert(false && "AliasAnalysisVisitor::bit2Field(): delta < 0");
        }
        return;
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

#ifdef DEBUG_LOAD_INSTR
        errs() << "Alias Analysis, in visitLoadInst() for instr: ";
        I.print(errs());
        errs() << "\n";
#endif
        Value* srcPointer = I.getPointerOperand();
        GEPOperator *gep = dyn_cast<GEPOperator>(I.getPointerOperand());
        if(gep && gep->getNumOperands() > 0 && gep->getPointerOperand() && !dyn_cast<GetElementPtrInst>(I.getPointerOperand())) {
#ifdef DEBUG_LOAD_INSTR
            errs() << "There is a GEP operator: ";
            gep->print(errs());
            errs() << "\n";
#endif
            //srcPointer = gep->getPointerOperand();
            //hz: to get the field sensitive point-to information and record it for the GEP operator value.
            srcPointer = visitGetElementPtrOperator(&I,gep);
        } else {
            if(!hasPointsToObjects(srcPointer)) {
#ifdef DEBUG_LOAD_INSTR
                errs() << "No point-to info, try to strip the pointer casts -0.\n";
#endif
                srcPointer = srcPointer->stripPointerCasts();
#ifdef DEBUG_LOAD_INSTR
                errs() << "After strip, the pointer is: ";
                srcPointer->print(errs());
                errs() << "\n";
#endif
            }
        }

        // strip pointer casts. if we cannot find any points to for the srcPointer.
        if(!hasPointsToObjects(srcPointer)) {
#ifdef DEBUG_LOAD_INSTR
            errs() << "No point-to info, try to strip the pointer casts -1.\n";
#endif
            srcPointer = srcPointer->stripPointerCasts();
#ifdef DEBUG_LOAD_INSTR
            errs() << "After strip, the pointer is: ";
            srcPointer->print(errs());
            errs() << "\n";
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
            errs() << "Load instruction does not point to any object.";
            I.print(errs());
            errs() << "\n";
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
        for(const std::pair<long, AliasObject*> &currObjPair:targetObjects) {
            // fetch objects that could be pointed by the field.
            // if this object is a function argument then
            // dynamically try to create an object, if we do not have any object
            currObjPair.second->fetchPointsToObjects(currObjPair.first, finalObjects, &I, finalObjects.empty());
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
                PointerPointsTo *newPointsToObj = new PointerPointsTo();
                newPointsToObj->targetPointer = &I;
                newPointsToObj->propogatingInstruction = &I;
                newPointsToObj->targetObject = currPto.second;
                newPointsToObj->fieldId = 0;
                newPointsToObj->dstfieldId = currPto.first;
                newPointsToInfo->insert(newPointsToInfo->end(), newPointsToObj);
            }
            // Just save the newly created set as points to set for this instruction.
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "Updating points to information for Load instruction:";
            I.print(dbgs());
            dbgs() << "\n";
#endif
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

    }

    void AliasAnalysisVisitor::visitStoreInst(StoreInst &I) {
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
        if(!hasPointsToObjects(targetValue)) {
            targetValue = targetValue->stripPointerCasts();
#ifdef DEBUG_STORE_INSTR
            dbgs() << "No point-to info for targetValue, try to strip the pointer casts -1.\n";
            dbgs() << "After strip, the targetValue is: " << InstructionUtils::getValueStr(targetValue) << "\n";
#endif
        }
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
        if(hasPointsToObjects(targetValue)) {

            // Get the src points to information.
            std::set<PointerPointsTo *> *srcPointsTo = getPointsToObjects(targetValue);

            if(!hasPointsToObjects(targetPointer)) {
                targetPointer = targetPointer->stripPointerCasts();
            }
            // Get the dst points to information.
            std::set<PointerPointsTo *> *dstPointsTo = getPointsToObjects(targetPointer);
#ifdef STRICT_STORE

            assert(dstPointsTo != nullptr);
#endif
            if(dstPointsTo == nullptr) {
#ifdef DEBUG_STORE_INSTR
                dbgs() << "Trying to store something into pointer, which does not point to anything\n";
#endif
                return;
            }


            // we need to create new points to information.
            std::set<PointerPointsTo *> *newPointsToInfo = new std::set<PointerPointsTo *>();
            newPointsToInfo->insert(dstPointsTo->begin(), dstPointsTo->end());

            //hz: "newPointsToInfo: is where we need to store into.
            if (newPointsToInfo->size() <= 1) {
                if (newPointsToInfo->size() == 1) {
                    //TargetPointer only has one point-to record.
#ifdef DEBUG_STORE_INSTR
                    dbgs() << "There is only 1 point-to record for the TargetPointer, *might* need a strong update.\n";
#endif
                    PointerPointsTo *dstPointsToObject = *(newPointsToInfo->begin());
                    // we have a pointer which points to only one object.
                    // Do a strong update
                    // Basic sanity
                    if(!((dstPointsToObject->targetPointer == targetPointer ||
                                dstPointsToObject->targetPointer == targetPointer->stripPointerCasts()) &&
                            dstPointsToObject->fieldId == 0)) {
                        dbgs() << "We're going to crash in AliasAnalysisVisitor::visitStoreInst() - strong update:( ...\n";
                        dbgs() << "Inst: " << InstructionUtils::getValueStr(&I) << "\n";
                        dbgs() << "dstPointsToObject->targetPointer: " << InstructionUtils::getValueStr(dstPointsToObject->targetPointer) << "\n";
                        dbgs() << "targetPointer: " << InstructionUtils::getValueStr(targetPointer) << "\n";
                        dbgs() << "targetPointer->stripPointerCasts(): " << InstructionUtils::getValueStr(targetPointer->stripPointerCasts()) << "\n";
                        dbgs() << (dstPointsToObject->targetPointer == targetPointer) << " | " << (dstPointsToObject->targetPointer == targetPointer->stripPointerCasts()) << "\n";
                        dbgs() << "dstPointsToObject->fieldId: " << dstPointsToObject->fieldId << "\n";
                    }
                    assert((dstPointsToObject->targetPointer == targetPointer ||
                                dstPointsToObject->targetPointer == targetPointer->stripPointerCasts()) &&
                            dstPointsToObject->fieldId == 0);

                    //OK, we need to change this points to.
                    PointerPointsTo *newDstPointsToObject = (PointerPointsTo *) dstPointsToObject->makeCopy();

                    // OK, now we got the target object to which the pointer points to.
                    // We are trying to store a pointer(*) into an object field

                    newDstPointsToObject->targetObject->performUpdate(newDstPointsToObject->dstfieldId,
                            srcPointsTo, &I);

                    // Now insert
                    newPointsToInfo->clear();
                    newPointsToInfo->insert(newPointsToInfo->begin(), newDstPointsToObject);
                } else {
                    // This is impossible.
                    // we are trying to store a value into pointer and the pointer
                    // cannot point to any object???
#ifdef DEBUG_STORE_INSTR
                    errs() << "Trying to store a value into a pointer, which does not point to any object.\n";
#endif
#ifdef STRICT_STORE
                    assert(false);
#endif
                }

            } else {
                //Ok, this pointer can point to multiple objects
                //Perform weak update for each of the dst pointer points to
#ifdef DEBUG_STORE_INSTR
                dbgs() << "Performing weak update since there are multiple point-to for the targetPointer..\n";
#endif
                newPointsToInfo->clear();
                for (PointerPointsTo *currPointsTo: *dstPointsTo) {
                    PointerPointsTo *newPointsToObj = (PointerPointsTo *) currPointsTo->makeCopy();
                    //Basic Sanity
                    if(!(newPointsToObj->targetPointer == targetPointer && newPointsToObj->fieldId == 0)) {
                        dbgs() << "We're going to crash in AliasAnalysisVisitor::visitStoreInst() - weak update:( ...\n";
                        dbgs() << "Inst: " << InstructionUtils::getValueStr(&I) << "\n";
                        dbgs() << "newPointsToObj->targetPointer: " << InstructionUtils::getValueStr(newPointsToObj->targetPointer) << "\n";
                        dbgs() << "targetPointer: " << InstructionUtils::getValueStr(targetPointer) << "\n";
                        dbgs() << (newPointsToObj->targetPointer == targetPointer) << "\n";
                        dbgs() << "newPointsToObj->fieldId: " << newPointsToObj->fieldId << "\n";
                    }
                    assert(newPointsToObj->targetPointer == targetPointer && newPointsToObj->fieldId == 0);
                    // perform weak update
                    newPointsToObj->targetObject->performWeakUpdate(newPointsToObj->dstfieldId, srcPointsTo, &I);
                    newPointsToInfo->insert(newPointsToInfo->end(), newPointsToObj);
                }
            }
            this->updatePointsToObjects(targetPointer, newPointsToInfo);
        } else {
            // OK, we are storing something, which have no points to information.
            // Check if destination is not a pointer to pointer, which means
            // src value should have some points to information.
            // tl;dr This branch should never be entered.
            // Ensure that we are not storing into pointer to pointer
            if(!this->inside_loop) {
#ifdef DEBUG_STORE_INSTR
                errs() << "Source pointer does not point to any thing:";
                targetValue->print(errs());
                errs() << "; Ignoring.\n";
#endif
            }
            //assert(!I.getPointerOperand()->getType()->getContainedType(0)->isPointerTy());
        }

    }

    // The following instructions are ignored.
    // we will deal with them, if we find them
    void AliasAnalysisVisitor::visitVAArgInst(VAArgInst &I) {
        assert(false);
    }

    void AliasAnalysisVisitor::visitVACopyInst(VACopyInst &I) {
        assert(false);
    }

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

        if(srcPointsTo != nullptr && dstPointsTo != nullptr) {
            // get all src objects.

            std::set<std::pair<long, AliasObject*>> srcAliasObjects;
            for(PointerPointsTo *currPointsTo:(*srcPointsTo)) {
                auto a = std::make_pair(currPointsTo->dstfieldId, currPointsTo->targetObject);
                if(srcAliasObjects.find(a) == srcAliasObjects.end()) {
                    srcAliasObjects.insert(a);
                }
            }

            std::set<std::pair<long, AliasObject*>> srcDrefObjects;
            for(auto a:srcAliasObjects) {
                a.second->fetchPointsToObjects(a.first, srcDrefObjects);
            }

            std::set<PointerPointsTo*> targetElements;
            for(auto a:srcDrefObjects) {
                PointerPointsTo *newRel = new PointerPointsTo();
                newRel->dstfieldId = a.first;
                newRel->targetObject = a.second;
                newRel->propogatingInstruction = &I;
                targetElements.insert(newRel);
            }

#ifdef DEBUG_CALL_INSTR
            dbgs() << "Got:" << targetElements.size() << " to add\n";
#endif
            for(auto a:(*dstPointsTo)) {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "Adding:" << targetElements.size() << "elements to the fieldid:" << a->dstfieldId << "\n";
#endif
                a->targetObject->performWeakUpdate(a->dstfieldId, &targetElements, &I);
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


    // Need to implement these
    VisitorCallback* AliasAnalysisVisitor::visitCallInst(CallInst &I, Function *currFunc,
            std::vector<Instruction *> *oldFuncCallSites,
            std::vector<Instruction *> *callSiteContext) {

#ifdef DEBUG_CALL_INSTR
        dbgs() << "AliasAnalysisVisitor::visitCallInst(): ";
        I.print(dbgs());
        dbgs() << "\n";
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
            } else {
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
            dbgs() << "Stitching return value for call instruction:";
            I.print(dbgs());
            dbgs() << "\n";
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
