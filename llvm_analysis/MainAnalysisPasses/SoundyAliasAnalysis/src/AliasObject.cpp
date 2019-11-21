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
        if (dyn_cast<StructType>(ty) && dyn_cast<StructType>(ty)->isOpaque()) {
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
            dbgs() << "validTyForOutsideObj(): it's an opaque struct type, cannot create the outside obj!\n";
#endif
            return false;
        }
        return true;
    }

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
        std::set<TaintFlag*> *fieldTaint = this->getFieldTaintInfo(srcfieldId);
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
        //Collapse the array/vector into a single element.
        if (this->targetType && dyn_cast<SequentialType>(this->targetType)) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "AliasObject::fetchPointsToObjects: the host is an array/vector, we will set the srcfieldId to 0.\n";
#endif
            srcfieldId = 0;
        }
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
                    expObjTy && dyn_cast<CompositeType>(expObjTy) && obj->targetObject->targetType != expObjTy) 
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
        }else if (dyn_cast<CompositeType>(this->targetType)) {
            //Boundary check
            if (!InstructionUtils::isIndexValid(this->targetType,srcfieldId)) {
                dbgs() << "!!! fetchPointsToObjects(): srcfieldId OOB!\n";
                dbgs() << "Below is the info about current AliasObject...\n";
                fetchPointsToObjects_log(srcfieldId, dstObjects, targetInstr, create_arg_obj);
                return;
            }
            ety = dyn_cast<CompositeType>(this->targetType)->getTypeAtIndex(srcfieldId);
        }else if (srcfieldId == 0) {
            ety = this->targetType;
        }else {
            return;
        }
        if (!ety) {
            //TODO: What can we do here?
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "Cannot decide the type of the dst element!\n";
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
            if (dyn_cast<CompositeType>(ety)) {
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
                ety = dyn_cast<CompositeType>(ety)->getTypeAtIndex((unsigned)0);
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
        }else if (dyn_cast<CompositeType>(e_pointto_ty) || e_pointto_ty->isVoidTy() || e_pointto_ty->isIntegerTy(8)) {
            // if there are no composite objects that this pointer field points to, generate a dummy object.
            //NOTE: we handle a special case here, sometimes the field type in the struct can be "void*" or "char*" ("i8*"), but it can be converted to "struct*" in the load,
            //if this is the case, we will create the dummy object based on the real converted type and still make this "void*/char*" field point to the new obj. 
            Type *real_ty = dyn_cast<CompositeType>(e_pointto_ty) ? e_pointto_ty : expObjTy;
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "fetchPointsToObjects(): the field pointee type is: " << InstructionUtils::getTypeStr(e_pointto_ty) << " real pointee type: " << InstructionUtils::getTypeStr(real_ty) << "\n";
#endif
            if(create_arg_obj || hostObj->isFunctionArg() || hostObj->isOutsideObject() || hostObj->isHeapLocation()) {
                if (!validTyForOutsideObj(real_ty)) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                    dbgs() << "fetchPointsToObjects(): the pointee type is invalid for an Outside object! Return...\n";
#endif
                    return;
                }
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
        if (this->targetType) {
            //Array collapse
            if (dyn_cast<SequentialType>(this->targetType)) {
#ifdef DEBUG_UPDATE_FIELD_POINT
                dbgs() << "updateFieldPointsTo(): sequential host, set srcfieldId to 0.\n";
#endif
                srcfieldId = 0;
            }
            //If the "srcfieldId" is an embedded struct/array, we need to recursively update the fieldPointsTo in the embedded object instead of current host object.
            if (dyn_cast<CompositeType>(this->targetType) && InstructionUtils::isIndexValid(this->targetType,srcfieldId)) {
                if (dyn_cast<CompositeType>(dyn_cast<CompositeType>(this->targetType)->getTypeAtIndex(srcfieldId))) {
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
            }
        }else {
            //Is this possible?
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "updateFieldPointsTo(): null type info for this host obj!\n";
#endif
        }
        std::set<AliasObject*> currObjects;
        // first get all objects that could be pointed by srcfieldId of the current object.
        this->getAllObjectsPointedByField(srcfieldId, currObjects);
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
        if (dyn_cast<CompositeType>(objTy)) {
            if (InstructionUtils::isIndexValid(objTy,this->dstfieldId)) {
                //TODO: when this->dstfieldId is 0, it will be tricky since we're actually not sure whether it points to the host obj itself, or the field 0 in the obj...
                //For now we return the type of the field 0.
                return dyn_cast<CompositeType>(objTy)->getTypeAtIndex(this->dstfieldId);
            }else {
                //This is a bug...
                dbgs() << "!!! ObjectPointsTo::getPointeeTy(): invalid dstfieldId, host obj ty: " << InstructionUtils::getTypeStr(objTy);
                dbgs() << " dstfieldId: " << this->dstfieldId << "\n";
                //TODO: return the nullptr or the obj type?
                return nullptr;
            }
        }
        return objTy;
    }

    void ObjectPointsTo::print(llvm::raw_ostream& OS) {
        if (this->targetObject) {
            OS << InstructionUtils::getTypeStr(this->targetObject->targetType) << " | " << this->fieldId << " -> " << this->dstfieldId;
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
                //We don't have a value/pointer here to generate a TaintFlag..
                //TODO:
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
                dbgs() << "!!!Type-based createOutsideObj(): trying to taint w/o existingTaints...\n";
#endif
            }
        }
        return newObj;
    }

    int updatePointsToRecord(Value *p, std::map<Value*,std::set<PointerPointsTo*>*> *currPointsTo, AliasObject *newObj, long fid, long dfid) {
        if (!newObj || !p) {
            return 0;
        }
        PointerPointsTo *newPointsTo = new PointerPointsTo();
        newPointsTo->targetPointer = p;
        newPointsTo->fieldId = fid;
        newPointsTo->dstfieldId = dfid;
        newPointsTo->targetObject = newObj;
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

    OutsideObject* createOutsideObj(Value *p, std::map<Value*,std::set<PointerPointsTo*>*> *currPointsTo, bool taint, std::set<TaintFlag*> *existingTaints) {
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
        updatePointsToRecord(p,currPointsTo,newObj);
        //Need taint?
        if (taint) {
            if (existingTaints && !existingTaints->empty()) {
                for (TaintFlag *currTaint : *existingTaints) {
                    newObj->taintAllFieldsWithTag(currTaint);
                }
            }else {
                //The original pointer is not tainted, treat it as a global state.
                TaintFlag *currFlag = new TaintFlag(p, true);
                newObj->taintAllFieldsWithTag(currFlag);
            }
            newObj->is_taint_src = true;
#ifdef DEBUG_CREATE_DUMMY_OBJ_IF_NULL
            dbgs() << "createOutsideObj(): set |is_taint_src| for the outside obj.\n";
#endif
        }
        return newObj;
    }

    AliasObject *createEmbObj(AliasObject *hostObj, long host_dstFieldId, Value *v, std::map<Value*, std::set<PointerPointsTo*>*> *currPointsTo) {
#ifdef DEBUG_CREATE_EMB_OBJ
        dbgs() << "Start createEmbObj()\n";
#endif
        AliasObject *newObj = nullptr;
        if (!hostObj || !hostObj->targetType) {
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "createEmbObj(): (!hostObj || !hostObj->targetType)\n";
#endif
            return nullptr;
        }
#ifdef DEBUG_CREATE_EMB_OBJ
        dbgs() << "createEmbObj(): host type: " << InstructionUtils::getTypeStr(hostObj->targetType) << " | " << host_dstFieldId << "\n";
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
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "createEmbObj(): find the previosuly created embed object!\n";
#endif
            //We have created that embedded object previously.
            newObj = hostObj->embObjs[host_dstFieldId];
        }
        if (!newObj || !InstructionUtils::same_types(newObj->targetType,ety)){
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
                newObj = DRCHECKER::createOutsideObj(v, currPointsTo, false, nullptr);
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
                dbgs() << "createHostObj(): we have created this parent object before!\n";
#endif
                return targetObj->parent;
            }else {
                //TODO: what to do in this case... for now let's just re-assign the parent object.
#ifdef DEBUG_CREATE_HOST_OBJ
                dbgs() << "!!! createHostObj(): found a previously created parent object but w/ different field or type!\n";
                dbgs() << "!!! createHostObj(): previous parent: " << InstructionUtils::getTypeStr(targetObj->parent->targetType) << " | " << targetObj->parent_field << ", id: " << (const void*)targetObj->parent << "\n";
#endif
                if (targetObj->parent->embObjs.find(targetObj->parent_field) != targetObj->parent->embObjs.end()) {
                    targetObj->parent->embObjs[targetObj->parent_field] = nullptr;
                }
                targetObj->parent = nullptr;
                targetObj->parent_field = 0;
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
        if (!ty || !fd || n.size() == 0) {
            return false;
        }
        //Be sure that "ty" exists in the "fd".
        if (fd->findTy(ty) < 0) {
            return false;
        }
        if (fd->host_tys.size() != fd->fid.size()) {
            return false;
        }
        int i = fd->findHostTy(ty);
        if (i < fd->host_tys.size() - 1) {
            //NOTE that this can also handle the case wherer "i = -1", which means "ty" is the innermost field and its direct host object is host_tys[0].
            std::string fn = InstructionUtils::getStFieldName(mod,dyn_cast<StructType>(fd->host_tys[i+1]),fd->fid[i+1]);
            return (n.find(fn) != std::string::npos);
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
                    bool nm_match = false;
                    if (n0.size() > 0 && n1.size() > 0) {
                        nm_match = (matchFieldName(mod,ty0,n0,fd) && matchFieldName(mod,ty1,n1,(*fds)[j]));
                    }else if (n0.size() > 0 || n1.size() > 0) {
                        nm_match = (n0.size() > 0 ? matchFieldName(mod,ty0,n0,fd) : matchFieldName(mod,ty1,n1,(*fds)[j]));
                    }
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
                funcs.insert(i->getFunction());
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
#ifdef DEBUG_CREATE_HOST_OBJ
                for (int j = 0; j < 2; ++j) {
                    dbgs() << "fid " << j << ": ";
                    for(unsigned id : (*tydesc)[res[i+j]]->fid) {
                        dbgs() << id << " ";
                    }
                }
                dbgs() << "\n";
#endif
                CandStructInf *inf = new CandStructInf();
                inf->fds = tydesc;
                inf->ind.push_back(res[i]);
                inf->ind.push_back(res[i+1]);
                cands->push_back(inf);
                if (rc == 2) {
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

    PointerPointsTo *getOrCreateHostObj(AliasObject *obj) {
        if (!obj) {
            return nullptr;
        }
#ifdef DEBUG_CREATE_HOST_OBJ
        dbgs() << "getOrCreateHostObj(): element obj: " << InstructionUtils::getTypeStr(obj->targetType) << "\n";
#endif
        PointerPointsTo *pto = new PointerPointsTo();
        //Is this an embedded object in a known host object?
        if (obj->parent) {
#ifdef DEBUG_CREATE_HOST_OBJ
            dbgs() << "getOrCreateHostObj(): There exists parent object from the record.\n";
#endif
            pto->targetObject = obj->parent;
            pto->dstfieldId = obj->parent_field;
            return pto;
        }
        Type *ty0 = obj->targetType;
        if (!ty0) {
            return nullptr;
        }
        /*
        //It's not embedded in any known object, but we can still do some inferences here, consider a very common case:
        //the kernel linked list mechanism will embed a "list_head" struct into every host object which needs to be linked,
        //we may have "list_head" A embedded in host A and "list_head" B pointed from "list_head" A, though we don't have
        //any records regarding B's host object, we can still infer its host object type (same as host A) and create a dummy
        //object.
        if (!obj->pointsFrom.empty()) {
            for (AliasObject *prev : obj->pointsFrom) {
                if (!prev) {
                    continue;
                }
                //TODO: currently we only consider one layer's points-from, maybe we need more..
                if (InstructionUtils::same_types(prev->targetType,obj->targetType)) {
                    if (prev->parent && prev->parent->targetType) {
                        AliasObject *hobj = DRCHECKER::createHostObj(obj,prev->parent->targetType,prev->parent_field);
                        if (!hobj) {
                            continue;
                        }
                        pto->targetObject = hobj;
                        pto->dstfieldId = prev->parent_field;
                        return pto;
                    }
                }
            }
        }
        */
        return nullptr;
    }

    //A typical and common scenario in which we need to call "getOrCreateHostObj()" is that in a "GEP i8 *ptr, index" IR the "ptr" points to
    //a certain object but is converted to i8*. then the "index" calculates a pointer pointing outside this object...
    //To find the host obj, what we want to do is to iterate over all struct types in the current module, then find the correct type(s)
    //that has properly distanced field types that matches both the base "ptr" and the pointer type produced by the "GEP" (we need to
    //figure out the true pointer type from the subsequent cast IRs).
    CandStructInf *inferContainerTy(Module *m,Value *v,Type *ty,long bitoff) {
#ifdef DEBUG_INFER_CONTAINER
        dbgs() << "inferContainerTy(): v: " << InstructionUtils::getValueStr(v) << " ty: " << InstructionUtils::getTypeStr(ty) << " bitoff: " << bitoff << "\n";
#endif
        if (!m || !v || !ty) {
#ifdef DEBUG_INFER_CONTAINER
            dbgs() << "inferContainerTy(): !m || !v || !ty\n";
#endif
            return nullptr;
        }
        DataLayout dl = m->getDataLayout();
        long tysz = dl.getTypeStoreSizeInBits(ty);
        //Analyze every single-index GEP w/ the same i8* srcPointer "v".
        std::vector<CandStructInf*> cands;
        bool init = true;
        std::set<Instruction*> insts;
        for (User *u : v->users()) {
            if (dyn_cast<Instruction>(u)) {
                insts.insert(dyn_cast<Instruction>(u));
            }
            GEPOperator *gep = dyn_cast<GEPOperator>(u);
            //Make sure it has a single index.
            if (!gep || gep->getNumOperands() != 2 || gep->getPointerOperand() != v) {
                continue;
            }
            //Get the constant index value.
            ConstantInt *CI = dyn_cast<ConstantInt>(gep->getOperand(1));
            if (!CI) {
                continue;
            }
            long index = CI->getSExtValue();
            //Make sure the base pointer is iN*.
            Type *bty = gep->getPointerOperandType();
            if (bty->isPointerTy()) {
                bty = bty->getPointerElementType();
            }
            if (!dyn_cast<IntegerType>(bty)) {
                continue;
            }
            unsigned width = dyn_cast<IntegerType>(bty)->getBitWidth();
            long resOff = bitoff + index * width;
#ifdef DEBUG_INFER_CONTAINER
            dbgs() << "inferContainerTy(): found one single-constant-index GEP using the same srcPointer: " << InstructionUtils::getValueStr(gep) << "\n";
            dbgs() << "inferContainerTy(): index: " << index << " width: " << width << " resOff: " << resOff << " current host type size: " << tysz << "\n";
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
            return nullptr;
        }
        //Ok now we have got a candidate container list.
        //We need to select a best candidate to return...
        sortCandStruct(&cands,&insts);
#ifdef DEBUG_INFER_CONTAINER
        for (int i = 0; i < cands.size(); ++i) {
            Type *t = (*cands[i]->fds)[0]->getOutermostTy();
            dbgs() << "inferContainerTy(): CAND " << i << " SCORE " << cands[i]->score << " : " << InstructionUtils::getTypeStr(t) << "\n"; 
            for (FieldDesc *fd : *(cands[i]->fds)) {
                fd->print(dbgs());
            }
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

    OutsideObject *getSharedObjFromCache(Type *ty) {
#ifdef DEBUG_SHARED_OBJ_CACHE
        dbgs() << "getSharedObjFromCache(): At the entrance. Type: " << InstructionUtils::getTypeStr(ty) << " currEntryFunc: " << DRCHECKER::currEntryFunc->getName().str() << "\n";
#endif
        if (!ty || !DRCHECKER::currEntryFunc) {
#ifdef DEBUG_SHARED_OBJ_CACHE
            dbgs() << "getSharedObjFromCache(): (!ty || !DRCHECKER::currEntryFunc)\n";
#endif
            return nullptr;
        }
        if (DRCHECKER::sharedObjCache.find(ty) == DRCHECKER::sharedObjCache.end()) {
#ifdef DEBUG_SHARED_OBJ_CACHE
            dbgs() << "getSharedObjFromCache(): No same-typed objs found in the cache.\n";
#endif
            return nullptr;
        }
        for (auto &e : DRCHECKER::sharedObjCache[ty]) {
            if (e.first != DRCHECKER::currEntryFunc) {
                for (OutsideObject *o : e.second) {
#ifdef DEBUG_SHARED_OBJ_CACHE
                    dbgs() << "getSharedObjFromCache(): Ty: " << InstructionUtils::getTypeStr(ty) << " currEntryFunc: " << DRCHECKER::currEntryFunc->getName().str() << " srcEntryFunc: " << e.first->getName().str();
                    dbgs() << " obj ID: " << (const void*)o << "\n";
#endif
                    return o;
                }
            }else {
                //This means there is already a same-typed object created previously when analyzing current entry function.
                //TODO: should we re-use this previous obj or create a new one?
#ifdef DEBUG_SHARED_OBJ_CACHE
                dbgs() << "getSharedObjFromCache(): Found a previously created obj by the current entry func.\n";
#endif
                break;
            }
        }
        return nullptr;
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

}
