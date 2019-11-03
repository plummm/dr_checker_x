#include "AliasObject.h"

using namespace llvm;

namespace DRCHECKER {

    std::map<Type*,std::map<Function*,std::set<OutsideObject*>>> sharedObjCache;

    Function *currEntryFunc = nullptr;

    void AliasObject::fetchPointsToObjects_log(long srcfieldId, std::set<std::pair<long, AliasObject*>> &dstObjects,
            Instruction *targetInstr, bool create_arg_obj) {
        dbgs() << "\n*********fetchPointsToObjects**********\n";
        dbgs() << "Current Inst: " << InstructionUtils::getValueStr(targetInstr) << "\n";
        dbgs() << "Object Type: " << InstructionUtils::getTypeStr(this->targetType) << "\n";
        dbgs() << "Object Ptr: " << InstructionUtils::getValueStr(this->getValue()) << "\n";
        dbgs() << "Obj ID: " << (const void*)this << "\n";
        if (this->getValue()){
            /*
               if(dyn_cast<Instruction>(this->targetVar)){
                    dbgs() << "\n";
                    dyn_cast<Instruction>(this->targetVar)->getFunction()->print(dbgs());
               }
             */
        }
        dbgs() << "Target Field: " << srcfieldId << "\n";
        dbgs() << "*******************\n";
    }

    //Taint the point-to object by field "srcfieldId" according to the field taint info.
    void AliasObject::taintSubObj(AliasObject *newObj, long srcfieldId, Instruction *targetInstr) {
        std::set<TaintFlag*> *fieldTaint = getFieldTaintInfo(srcfieldId);
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        dbgs() << "AliasObject::taintSubObj(): Trying to get taint for field:" << srcfieldId << " of host object: " << (const void*)this << "\n";
#endif
        if(fieldTaint != nullptr) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::taintSubObj(): Adding taint of field:" << srcfieldId << " to sub object: " << (const void*)newObj << "\n";
#endif
            for(auto existingTaint:*fieldTaint) {
                TaintFlag *newTaint = new TaintFlag(existingTaint,targetInstr,targetInstr);
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
                TaintFlag *newTaint = new TaintFlag(this->all_contents_taint_flag,targetInstr,targetInstr);
                newObj->taintAllFieldsWithTag(newTaint);
                newObj->is_taint_src = true;
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "##Set |is_taint_src| to true.\n";
#endif
            }
        }
    }

    //An improved version of "fetchPointsToObjects", we need to consider the type of each field.
    void AliasObject::fetchPointsToObjects(long srcfieldId, std::set<std::pair<long, AliasObject*>> &dstObjects,
            Instruction *targetInstr, bool create_arg_obj) {
        /***
         * Get all objects pointed by field identified by srcfieldID
         *
         * i.e if a field does not point to any object.
         * Automatically generate an object and link it with srcFieldId
         */
        //assert(this->targetType);
        //assert(this->targetType->isStructTy());
        /*
        if (!this->targetType || !this->targetType->isStructTy()) {
            //fallback method
            return this->fetchPointsToObjects_default(srcfieldId,dstObjects,targetInstr,create_arg_obj);
        }
        */
        //What's the expected type of the fetched point-to object?
        Type *expFieldTy = nullptr;
        Type *expObjTy = nullptr;
        //TODO: deal with other types of insts that can invoke "fetchPointsToObjects" in its handler.
        if (targetInstr && dyn_cast<LoadInst>(targetInstr)) {
            expFieldTy = targetInstr->getType();
            if (expFieldTy->isPointerTy()) {
                expObjTy = expFieldTy->getPointerElementType();
            }
        }
        bool hasObjects = false;
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
        fetchPointsToObjects_log(srcfieldId, dstObjects, targetInstr, create_arg_obj);
#endif
        for(ObjectPointsTo *obj : pointsTo) {
            if(obj->fieldId == srcfieldId && obj->targetObject) {
                //We handle a special case here:
                //Many malloc'ed HeapLocation object can be of the type i8*, while only in the later code the pointer will be converted to a certain struct*,
                //we choose to do this conversion here, specifically we need to:
                //(1) change the object type to the "expObjTy",
                //(2) setup the taint information properly.
#ifdef DEBUG_CHANGE_HEAPLOCATIONTYPE
                //dbgs() << "AliasObject::fetchPointsToObjects: isHeapLocation: " << (obj->targetObject && obj->targetObject->isHeapLocation()) << " dstField: " << obj->dstfieldId;
                //dbgs() << " expObjTy: " << InstructionUtils::getTypeStr(expObjTy) << "\n";
#endif
                if (obj->dstfieldId == 0 && obj->targetObject && obj->targetObject->isHeapLocation() && 
                    expObjTy && expObjTy->isStructTy() && obj->targetObject->targetType != expObjTy) 
                {
#ifdef DEBUG_CHANGE_HEAPLOCATIONTYPE
                    dbgs() << "AliasObject::fetchPointsToObjects: isHeapLocation: " << (obj->targetObject && obj->targetObject->isHeapLocation()) << " dstField: " << obj->dstfieldId;
                    dbgs() << " expObjTy: " << InstructionUtils::getTypeStr(expObjTy) << "\n";
                    dbgs() << "AliasObject::fetchPointsToObjects: Change type of the HeapLocation.\n";
#endif
                    //Change type.
                    obj->targetObject->targetType = expObjTy;
                    //Do the taint accordingly.
                    this->taintSubObj(obj->targetObject,srcfieldId,targetInstr);
                }
                auto p = std::make_pair(obj->dstfieldId, obj->targetObject);
                if(std::find(dstObjects.begin(), dstObjects.end(), p) == dstObjects.end()) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                    dbgs() << "Found an obj in |pointsTo| records:\n";
                    dbgs() << "Type: " << InstructionUtils::getTypeStr(obj->targetObject->targetType) << " | " << obj->dstfieldId << " | is_taint_src:" << obj->targetObject->is_taint_src << "\n";
                    dbgs() << "Val: " << InstructionUtils::getValueStr(obj->targetObject->getValue()) << " ID: " << (const void*)(obj->targetObject) << "\n";
#endif
                    dstObjects.insert(dstObjects.end(), p);
                    hasObjects = true;
                }
            }
        }
        if(hasObjects || InstructionUtils::isAsanInst(targetInstr)) {
            return;
        }
        //Below we try to create a dummy object.
        //Get the type of the field for which we want to get the pointee.
        Type *ety = nullptr;
        if (!this->targetType) {
            return;
        }else if (this->targetType->isStructTy()) {
            if (srcfieldId >= this->targetType->getStructNumElements()) {
                //This is a serious bug possibly due to "cast" IR.
                dbgs() << "!!! fetchPointsToObjects(): srcfieldId out of bound (struct)!\n";
                dbgs() << "Below is the info about current AliasObject...\n";
                fetchPointsToObjects_log(srcfieldId, dstObjects, targetInstr, create_arg_obj);
                return;
            }
            ety = this->targetType->getStructElementType(srcfieldId);
        }else if (dyn_cast<SequentialType>(this->targetType)) {
            SequentialType *seqTy = dyn_cast<SequentialType>(this->targetType);
            if (srcfieldId >= seqTy->getNumElements()) {
                dbgs() << "!!! fetchPointsToObjects(): srcfieldId out of bound (array/vector)!\n";
                dbgs() << "Below is the info about current AliasObject...\n";
                fetchPointsToObjects_log(srcfieldId, dstObjects, targetInstr, create_arg_obj);
                return;
            }
            ety = seqTy->getElementType();
        }else {
            return;
        }
        if (!ety) {
            //TODO: What can we do here?
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "Cannot decide the type of the dst element!\n";
            fetchPointsToObjects_log(srcfieldId, dstObjects, targetInstr, create_arg_obj);
#endif
            return;
        }
        //Get the pointee type of the dst field.
        //There will be several cases here:
        //(1) The dst element is a pointer, then we can try to create a dummy obj for it since there are no related records in "pointsTo";
        //(2) The dst element is an embedded struct/array, if this is the case we need to recursively extract the first field of it until we get a non-emb-struct field, then we can decide the type of dummy obj to create.
        //(3) No type information for the dst element is available, return directly.
        Type *e_pointto_ty = nullptr;
        AliasObject *hostObj = this;
        long fid = srcfieldId;
        while (!ety->isPointerTy()) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "fetchPointsToObjects(): dst field " << fid << " is not a pointer: " << InstructionUtils::getTypeStr(ety) << "\n"; 
#endif
            if (ety->isStructTy() || ety->isArrayTy()) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "fetchPointsToObjects(): Try to create an emb obj for the dst field.\n"; 
#endif
                AliasObject *newObj = DRCHECKER::createEmbObj(hostObj, fid);
                if (!newObj) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                    dbgs() << "!!! fetchPointsToObjects(): Failed to create the emb obj.\n"; 
#endif
                    break;
                }
                hostObj = newObj;
                fid = 0;
                if (ety->isStructTy()) {
                    ety = ety->getStructElementType(0);
                }else if (ety->isArrayTy()) {
                    ety = ety->getArrayElementType();
                }
            }else {
                //TODO: Can we handle any other dst element types?
                return;
            }
        }
        if (ety->isPointerTy()) {
            e_pointto_ty = ety->getPointerElementType();
        }else {
            return;
        }
        //TODO: replace the below "this->" w/ possibly newly created emb obj.
        //Create the dummy obj according to the dst element type.
        if (!e_pointto_ty || !hostObj) {
            return;
        }else if (e_pointto_ty->isFunctionTy()) {
            //This is a function pointer w/o point-to function, which can cause trobule later in resolving indirect function call.
            //We can try to do some smart resolving here by looking at the same-typed global constant objects.
#ifdef SMART_FUNC_PTR_RESOLVE
            std::vector<Function*> candidateFuncs;
            hostObj->getPossibleMemberFunctions(targetInstr, dyn_cast<FunctionType>(e_pointto_ty), hostObj->targetType, fid, candidateFuncs);
            for (Function *func : candidateFuncs) {
                GlobalObject *newObj = new GlobalObject(func);

                //Update pointsFrom info in the newly created obj.
                hostObj->addToPointsFrom(newObj);

                //Update points-to
                std::set<PointerPointsTo*> dstPointsTo;
                PointerPointsTo *newPointsToObj = new PointerPointsTo();
                newPointsToObj->propogatingInstruction = targetInstr;
                newPointsToObj->targetObject = newObj;
                newPointsToObj->fieldId = fid;
                newPointsToObj->dstfieldId = 0;
                //TODO: newPointsToObj->targetPointer may not need be set since "pointsTo" will only contain "ObjectPointsTo" type that doesn't have targetPointer.
                dstPointsTo.insert(newPointsToObj);
                hostObj->updateFieldPointsTo(fid,&dstPointsTo,targetInstr);

                dstObjects.insert(dstObjects.end(), std::make_pair(0, newObj));
            }
#endif
        }else if (e_pointto_ty->isStructTy() || e_pointto_ty->isVoidTy()) {
            // if there are no struct objects that this pointer field points to, generate a dummy object.
            //NOTE: we handle a special case here, sometimes the field type in the struct can be "void*", but it can be converted to "struct*" in the load,
            //if this is the case, we will create the dummy object based on the real converted type and still make this "void*" field point to the new obj. 
            Type *real_ty = e_pointto_ty->isStructTy() ? e_pointto_ty : expObjTy;
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "fetchPointsToObjects(): the field pointee type is: " << InstructionUtils::getTypeStr(e_pointto_ty) << " real pointee type: " << InstructionUtils::getTypeStr(real_ty) << "\n";
#endif
            if (!real_ty || !real_ty->isStructTy()) {
                return;
            }
            if(create_arg_obj || hostObj->isFunctionArg() || hostObj->isOutsideObject()) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "Creating a new dummy AliasObject...\n";
#endif
                OutsideObject *newObj = new OutsideObject(targetInstr,real_ty);
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "New obj Id: " << (const void*)newObj << "\n";
#endif
                newObj->auto_generated = true;
                // get the taint for the field and add that taint to the newly created object
                hostObj->taintSubObj(newObj,fid,targetInstr);

                //Update the pointsFrom info in the newly created obj.
                hostObj->addToPointsFrom(newObj);

                //Handle some special cases like mutual point-to in linked list node "list_head".
                hostObj->handleSpecialFieldPointTo(newObj,fid,targetInstr);

                //Update points-to
                std::set<PointerPointsTo*> dstPointsTo;
                PointerPointsTo *newPointsToObj = new PointerPointsTo();
                newPointsToObj->propogatingInstruction = targetInstr;
                newPointsToObj->targetObject = newObj;
                newPointsToObj->fieldId = fid;
                // this is the field of the newly created object to which
                // new points to points to
                newPointsToObj->dstfieldId = 0;
                //TODO: newPointsToObj->targetPointer may not need be set since "pointsTo" will only contain "ObjectPointsTo" type that doesn't have targetPointer.
                dstPointsTo.insert(newPointsToObj);
                //NOTE: if we reach here, then there must be no point-to records for this "fid" yet, so we can directly use updateFieldPointsTo to do a strong update.
                hostObj->updateFieldPointsTo(fid,&dstPointsTo,targetInstr);

                dstObjects.insert(dstObjects.end(), std::make_pair(0, newObj));
            }
        }
    }

    void AliasObject::updateFieldPointsTo(long srcfieldId, std::set<PointerPointsTo*>* dstPointsTo, Instruction *propogatingInstr) {
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
        //If the "srcfieldId" is an embedded struct/array, we need to update the fieldPointsTo in the embedded object instead of current host object.
        if (this->targetType && this->targetType->isStructTy() &&
            srcfieldId >= 0 && srcfieldId < this->targetType->getStructNumElements() && 
            dyn_cast<CompositeType>(this->targetType->getStructElementType(srcfieldId))) {
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "updateFieldPointsTo(): The target field is an embedded object, we need to update the embedded object then..\n";
#endif
            //NOTE: this is actually getOrCreateEmbObj()
            AliasObject *eobj = createEmbObj(this,srcfieldId);
            if (eobj) {
                return eobj->updateFieldPointsTo(0,dstPointsTo,propogatingInstr);
            }else {
                //TODO: What should we do here...
#ifdef DEBUG_UPDATE_FIELD_POINT
                dbgs() << "updateFieldPointsTo(): Failed to create the embedded obj!\n";
#endif
            }
        }
        std::set<AliasObject*> currObjects;
        // first get all objects that could be pointed by srcfieldId of the current object.
        getAllObjectsPointedByField(srcfieldId, currObjects);
        //Add all objects that are in the provided set by changing the field id.
        for (PointerPointsTo *currPointsTo: *dstPointsTo) {
            // insert points to information only, if it is not present.
            if(currObjects.find(currPointsTo->targetObject) == currObjects.end()) {
                ObjectPointsTo *newPointsTo = currPointsTo->makeCopy();
                newPointsTo->fieldId = srcfieldId;
                newPointsTo->propogatingInstruction = propogatingInstr;
#ifdef DEBUG_UPDATE_FIELD_POINT
                dbgs() << "updateFieldPointsTo(), add point-to: ";
                newPointsTo->print(dbgs());
#endif
                this->pointsTo.push_back(newPointsTo);
                //hz: don't forget the "pointsFrom", it is a double link list...
                //TODO
                //this->addToPointsFrom(newPointsTo->targetObject);
            }
        }
    }

    Type *ObjectPointsTo::getPointeeTy() {
        if (!this->targetObject) {
            return nullptr;
        }
        Type *objTy = this->targetObject->targetType;
        if (!objTy) {
            return nullptr;
        }
        if (objTy->isStructTy()) {
            if (this->dstfieldId < 0) {
                //Is this possible?
                return objTy;
            }else if (this->dstfieldId == 0) {
                //TODO: this is subtle... We're actually not sure whether it points to the host obj itself, or the field 0 in the obj...
                //For now we return the type of the field 0.
                return objTy->getStructElementType(0);
            }else if (this->dstfieldId < objTy->getStructNumElements()) {
                return objTy->getStructElementType(this->dstfieldId);
            }else {
                //This is a bug...
                dbgs() << "!!! ObjectPointsTo::getPointeeTy(): dstfieldId exceeds the limit, host obj ty: " << InstructionUtils::getTypeStr(objTy);
                dbgs() << " dstfieldId: " << this->dstfieldId << "\n";
                //TODO: return the nullptr or the obj type?
                return nullptr;
            }
        }
        //TODO: what if the targetObj is an array?
        return objTy;
    }

    void ObjectPointsTo::print(llvm::raw_ostream& OS) {
        if (this->targetObject) {
            OS << InstructionUtils::getTypeStr(this->targetObject->targetType) << " | " << this->fieldId << " -> " << this->dstfieldId;
            OS << " Tgt Obj ID: " << (const void*)(this->targetObject) << "\n";
        }
    }

}
