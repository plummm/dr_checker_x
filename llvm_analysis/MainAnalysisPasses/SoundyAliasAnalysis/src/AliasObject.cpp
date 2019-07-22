#include "AliasObject.h"

using namespace llvm;

namespace DRCHECKER {

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
        dbgs() << "Trying to get taint for field:" << srcfieldId << " for object:" << this << "\n";
#endif
        if(fieldTaint != nullptr) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
            dbgs() << "Adding taint for field:" << srcfieldId << " for object:" << newObj << "\n";
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
                dbgs() << "Trying to get field from an object whose contents are fully tainted\n";
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
        if (!this->targetType || !this->targetType->isStructTy()) {
            //fallback method
            return this->fetchPointsToObjects_default(srcfieldId,dstObjects,targetInstr,create_arg_obj);
        }
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
                dbgs() << "AliasObject::fetchPointsToObjects: isHeapLocation: " << (obj->targetObject && obj->targetObject->isHeapLocation()) << " dstField: " << obj->dstfieldId;
                dbgs() << " expObjTy: " << InstructionUtils::getTypeStr(expObjTy) << "\n";
#endif
                if (obj->dstfieldId == 0 && obj->targetObject && obj->targetObject->isHeapLocation() && 
                    expObjTy && expObjTy->isStructTy() && obj->targetObject->targetType != expObjTy) 
                {
#ifdef DEBUG_CHANGE_HEAPLOCATIONTYPE
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
        if(hasObjects) {
            return;
        }
        //Below we try to create a dummy object.
        if (srcfieldId >= this->targetType->getStructNumElements()) {
            //This is a serious bug possibly due to "cast" IR.
            dbgs() << "!!! fetchPointsToObjects() outside: srcfieldId out of bound!\n";
            dbgs() << "Below is the info about current AliasObject...\n";
            fetchPointsToObjects_log(srcfieldId, dstObjects, targetInstr, create_arg_obj);
            return;
        }
        //NOTE: "pointsTo" should only store point-to information for the pointer fields.
        //So if "hasObjects" is false, we need to first ensure that the field is a pointer before creating new objects.
        Type *ety = this->targetType->getStructElementType(srcfieldId);
        if (!ety->isPointerTy()) {
            return;
        }
        Type *e_pointto_ty = ety->getPointerElementType();
        if (e_pointto_ty->isFunctionTy()) {
            //This is a function pointer w/o point-to function, which can cause trobule later in resolving indirect function call.
            //We can try to do some smart resolving here by looking at the same-typed global constant objects.
#ifdef SMART_FUNC_PTR_RESOLVE
            std::vector<Function*> candidateFuncs;
            this->getPossibleMemberFunctions(targetInstr, dyn_cast<FunctionType>(e_pointto_ty), this->targetType, srcfieldId, candidateFuncs);
            for (Function *func : candidateFuncs) {
                GlobalObject *newObj = new GlobalObject(func);
                ObjectPointsTo *newPointsToObj = new ObjectPointsTo();
                newPointsToObj->propogatingInstruction = targetInstr;
                newPointsToObj->targetObject = newObj;
                newPointsToObj->fieldId = srcfieldId;
                newPointsToObj->dstfieldId = 0;

                // Record the pointsFrom info in the newly created obj.
                newObj->pointsFrom.push_back(this);

                pointsTo.push_back(newPointsToObj);
                dstObjects.insert(dstObjects.end(), std::make_pair(0, newObj));
            }
#endif
        }else if (e_pointto_ty->isStructTy()) {
            // if there are no struct objects that this pointer field points to, generate a dummy object.
            if(create_arg_obj || this->isFunctionArg() || this->isOutsideObject()) {
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "Creating a new dummy AliasObject...\n";
#endif
                OutsideObject *newObj = new OutsideObject(targetInstr,e_pointto_ty);
#ifdef DEBUG_FETCH_POINTS_TO_OBJECTS
                dbgs() << "New obj Id: " << (const void*)newObj << "\n";
#endif
                ObjectPointsTo *newPointsToObj = new ObjectPointsTo();
                newPointsToObj->propogatingInstruction = targetInstr;
                newPointsToObj->targetObject = newObj;
                newPointsToObj->fieldId = srcfieldId;
                // this is the field of the newly created object to which
                // new points to points to
                newPointsToObj->dstfieldId = 0;
                newObj->auto_generated = true;
                // Record the pointsFrom info in the newly created obj.
                newObj->pointsFrom.push_back(this);

                // get the taint for the field and add that taint to the newly created object
                this->taintSubObj(newObj,srcfieldId,targetInstr);

                //insert the newly create object.
                this->pointsTo.push_back(newPointsToObj);

                dstObjects.insert(dstObjects.end(), std::make_pair(0, newObj));
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

}
