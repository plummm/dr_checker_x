//
// Created by machiry on 10/24/16.
//

#ifndef PROJECT_ALIASOBJECT_H
#define PROJECT_ALIASOBJECT_H
#include <set>
#include <llvm/Support/Debug.h>
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include "TaintInfo.h"
#include "../../Utils/include/CFGUtils.h"

using namespace llvm;
#ifdef DEBUG
#undef DEBUG
#endif

//hz: some debug output options.
//#define DEBUG_OUTSIDE_OBJ_CREATION
#define ENABLE_SUB_OBJ_CACHE
#define SMART_FUNC_PTR_RESOLVE
#define DEBUG_SMART_FUNCTION_PTR_RESOLVE
#define DEBUG_FETCH_POINTS_TO_OBJECTS
#define DEBUG_CHANGE_HEAPLOCATIONTYPE
#define DEBUG_UPDATE_FIELD_POINT
#define DEBUG_UPDATE_FIELD_TAINT
#define DEBUG_CREATE_DUMMY_OBJ_IF_NULL
#define DEBUG_CREATE_EMB_OBJ
#define DEBUG_CREATE_EMB_OBJ
#define DEBUG_CREATE_HOST_OBJ
#define DEBUG_CREATE_HOST_OBJ
#define DEBUG_INFER_CONTAINER
#define DEBUG_SPECIAL_FIELD_POINTTO
#define DEBUG_SHARED_OBJ_CACHE

namespace DRCHECKER {
//#define DEBUG_FUNCTION_ARG_OBJ_CREATION

    class AliasObject;

    /***
     * Handles general points to relation.
     */
    class ObjectPointsTo {
    public:
        // field id, if the parent object is a structure.
        long fieldId;
        // field id of the destination object to which this pointer points tp
        long dstfieldId;
        // object to which we point to.
        AliasObject *targetObject;
        // instruction which resulted in this points to information.
        //Value* propogatingInstruction;
        InstLoc *propogatingInst;
        //Whether this pto record is a weak update (e.g. the original dst pointer points to multiple locations in multiple objects,
        //so we are not sure whether this pto will be for sure updated for a certain object field at the 'propogatingInst').
        //NOTE that this concept is only useful when updating the object fieldPointsTo (i.e. for address-taken llvm objects), while for top-level variables (e.g. %x),
        //when we update its pto record we always know which top-level variable is to be updated (i.e. always a strong update).
        bool is_weak = false;
        //For customized usage.
        //E.g. when processing GEP, sometimes we may convert all indices into a single offset and skip "processGEPMultiDimension", use this flag to indicate this.
        int flag = 0;
        //indicates whether this pto record is currently active (e.g. may be invalidated by another strong post-dom pto update.).
        bool is_active = true;

        ObjectPointsTo() {
            this->flag = 0;
            this->is_active = true;
        }

        ~ObjectPointsTo() {
        }

        ObjectPointsTo(ObjectPointsTo *srcObjPointsTo) {
            this->fieldId = srcObjPointsTo->fieldId;
            this->dstfieldId = srcObjPointsTo->dstfieldId;
            this->targetObject = srcObjPointsTo->targetObject;
            this->propogatingInst = srcObjPointsTo->propogatingInst;
            this->is_weak = srcObjPointsTo->is_weak;
            this->flag = 0;
            this->is_active = srcObjPointsTo->is_active;
        }

        ObjectPointsTo(long fieldId, AliasObject *targetObject, long dstfieldId, InstLoc *propogatingInst = nullptr, bool is_Weak = false) {
            this->fieldId = fieldId;
            this->targetObject = targetObject;
            this->dstfieldId = dstfieldId;
            this->propogatingInst = propogatingInst;
            this->is_weak = is_weak;
            this->flag = 0;
            this->is_active = true;
        }

        virtual ObjectPointsTo* makeCopy() {
            return new ObjectPointsTo(this);
        }

        //NOTE: this comparison doesn't consider the additional properties including "propogatingInst" and "is_weak"
        virtual bool isIdenticalPointsTo(const ObjectPointsTo *that) const {
            if (!that) {
                return false;
            }
            return this->targetObject == that->targetObject &&
                   this->fieldId == that->fieldId &&
                   this->dstfieldId == that->dstfieldId;
        }

        virtual bool pointsToSameObject(const ObjectPointsTo *that) const {
            if(that != nullptr) {
                return this->targetObject == that->targetObject && this->dstfieldId == that->dstfieldId;
            }
            return false;
        }

        virtual long getTargetType() const {
            // Simple polymorphism.
            return 1;
        }

        /*virtual std::ostream& operator<<(std::ostream& os, const ObjectPointsTo& obj) {
            os << "Field :" << fieldId << " points to " << dstfieldId <<" of the object, with ID:" << obj.targetObject;
            return os;
        }*/
        friend llvm::raw_ostream& operator<<(llvm::raw_ostream& os, const ObjectPointsTo& obj) {
            os << "Field :" << obj.fieldId << " points to " << obj.dstfieldId <<" of the object, with ID:" << obj.targetObject;
            return os;
        }

        void print(llvm::raw_ostream& OS);

        bool inArray(Type *ety);
    };


    /***
     * Handles the pointer point to relation.
     */
    class PointerPointsTo: public ObjectPointsTo {
    public:
        const static long TYPE_CONST=2;
        // The src pointer that points to
        Value *targetPointer;

        PointerPointsTo(PointerPointsTo *srcPointsTo): ObjectPointsTo(srcPointsTo) {
            this->targetPointer = srcPointsTo->targetPointer;
        }

        PointerPointsTo(Value *targetPointer, long fieldId, AliasObject *targetObject, long dstfieldId, 
                        InstLoc *propogatingInst = nullptr, bool is_Weak = false): 
                        ObjectPointsTo(fieldId, targetObject, dstfieldId, propogatingInst, is_Weak) {
                            this->targetPointer = targetPointer;
                        }

        PointerPointsTo() {

        }

        ObjectPointsTo* makeCopy() {
            return new PointerPointsTo(this);
        }

        PointerPointsTo* makeCopyP() {
            return new PointerPointsTo(this);
        }

        long getTargetType() const {
            // Simple polymorphism.
            return PointerPointsTo::TYPE_CONST;
        }

        /*
        bool isIdenticalPointsTo(const ObjectPointsTo *that) const {
            if (that && that->getTargetType() == PointerPointsTo::TYPE_CONST) {
                PointerPointsTo* actualObj = (PointerPointsTo*)that;
                return this->targetPointer == actualObj->targetPointer &&
                       this->targetObject == actualObj->targetObject &&
                       this->fieldId == actualObj->fieldId &&
                       this->dstfieldId == actualObj->dstfieldId;
            }
            return false;
        }
        */

        /*std::ostream& operator<<(std::ostream& os, const ObjectPointsTo& obj) {
            PointerPointsTo* actualObj = (PointerPointsTo*)(&obj);
            os << "Pointer:";
            os << actualObj->targetPointer->getName().str();
            os << " from field:" << fieldId <<" points to field:"<< dstfieldId <<" of the object, with ID:" << this->targetObject;
            return os;
        }*/

        friend llvm::raw_ostream& operator<<(llvm::raw_ostream& os, const PointerPointsTo& obj) {
            PointerPointsTo* actualObj = (PointerPointsTo *)(&obj);
            os << "Pointer:";
            os << actualObj->targetPointer->getName().str();
            os << " from field:" << obj.fieldId <<" points to field:"<< obj.dstfieldId <<" of the object, with ID:" << obj.targetObject;
            return os;
        }

        void print(llvm::raw_ostream& OS);
    };


    static unsigned long idCount;

    static unsigned long getCurrID() {
        return idCount++;
    }

    /***
     * The alias object. Refer Definition 3.7 of the paper.
     */
    class AliasObject {
    public:
        Type* targetType;
        // All pointer variables that can point to this object.
        std::vector<PointerPointsTo *> pointersPointsTo;
        // This represents points from information, all objects which can point to this.
        // The key is the src object, the value is the pto records in src object that point to this obj.
        std::map<AliasObject*,std::set<ObjectPointsTo*>> pointsFrom;
        // All Objects that could be pointed by this object.
        // The key is the field number, the value is all pto records of this field.
        std::map<long,std::set<ObjectPointsTo*>> pointsTo;
        // The reference instruction of this AliasObject (usually the inst where this obj is created.).
        Instruction *refInst = nullptr;

        //Information needed for Taint Analysis.
        // fields that store information which is tainted.
        std::vector<FieldTaint*> taintedFields;

        bool auto_generated = false;

        // field to indicate that all contents of this object
        // are tainted or not.
        bool all_contents_tainted = false;
        TaintFlag *all_contents_taint_flag = nullptr;

        // flag which indicates whether the object is initialized or not.
        // by default every object is initialized.
        bool is_initialized = true;
        // the set of instructions which initialize this object
        std::set<Instruction*> initializingInstructions;

        unsigned long id;

        //hz: indicate whether this object is a taint source.
        bool is_taint_src = false;

        //hz: This maps the field to the corresponding object (embedded) if the field is an embedded struct in the host object.
        std::map<long,AliasObject*> embObjs;

        //hz: it's possible that this obj is embedded in another obj.
        AliasObject *parent;
        long parent_field;

        unsigned long getID() const{
            return this->id;
        }

        AliasObject(AliasObject *srcAliasObject) {
            assert(srcAliasObject != nullptr);
            this->targetType = srcAliasObject->targetType;
            this->pointersPointsTo.insert(this->pointersPointsTo.end(), srcAliasObject->pointersPointsTo.begin(),
                                          srcAliasObject->pointersPointsTo.end());
            this->pointsFrom = srcAliasObject->pointsFrom;
            this->pointsTo = srcAliasObject->pointsTo;
            this->id = getCurrID();

            this->is_initialized = srcAliasObject->is_initialized;
            this->initializingInstructions.insert(srcAliasObject->initializingInstructions.begin(),
                                                  srcAliasObject->initializingInstructions.end());
            //this->is_taint_src = srcAliasObject->is_taint_src;
            this->embObjs = srcAliasObject->embObjs;
            this->parent = srcAliasObject->parent;
            this->parent_field = srcAliasObject->parent_field;
            this->refInst = srcAliasObject->refInst;
        }

        AliasObject() {
            //hz: init some extra fields
            this->id = getCurrID();
            this->parent = nullptr;
            this->parent_field = 0;
            this->refInst = nullptr;
        }

        ~AliasObject() {
            // delete all object pointsTo and the related pointsFrom in other objects.
            for (auto &x : pointsTo) {
                for (ObjectPointsTo *pto : x.second) {
                    if (pto->targetObject) {
                        pto->targetObject->erasePointsFrom(this,pto);
                    }
                    delete(pto);
                }
            }

            // delete all field taint.
            for(auto ft:taintedFields) {
                delete(ft);
            }
        }

        //If "act" is negative, return # of all pto on file, otherwise, only return active/inactive pto records.
        unsigned long countObjectPointsTo(long srcfieldId, int act = -1) {
            /***
             * Count the number of object-field combinations that could be pointed by
             * a field (i.e srcfieldId).
            */
            if (this->pointsTo.find(srcfieldId) == this->pointsTo.end()) {
                return 0;
            }
            if (act < 0) {
                return this->pointsTo[srcfieldId].size();
            }
            int num = 0;
            for (ObjectPointsTo *pto : this->pointsTo[srcfieldId]) {
                if (pto && pto->is_active == !!act) {
                    ++num;
                }
            }
            return num;
        }

        //update the "pointsFrom" records.
        bool addPointsFrom(AliasObject *srcObj, ObjectPointsTo *pto) {
            if (!srcObj || !pto) {
                return false;
            }
            //validity check
            if (pto->targetObject != this) {
                return false;
            }
            if (this->pointsFrom.find(srcObj) == this->pointsFrom.end()) {
                this->pointsFrom[srcObj].insert(pto);
            }else {
                //Detect the duplication.
                if(std::find_if(this->pointsFrom[srcObj].begin(), this->pointsFrom[srcObj].end(), [pto](const ObjectPointsTo *n) {
                            return  n->fieldId == pto->fieldId && n->dstfieldId == pto->dstfieldId;
                            }) == this->pointsFrom[srcObj].end()) {
                    this->pointsFrom[srcObj].insert(pto);
                }
            }
            return true;
        }

        //If "act" is negative, the specified pto record will be removed, otherwise, its "is_active" field will be set to "act".
        bool erasePointsFrom(AliasObject *srcObj, ObjectPointsTo *pto, int act = -1) {
            if (!srcObj || !pto || this->pointsFrom.find(srcObj) == this->pointsFrom.end()) {
                return true;
            }
            for (auto it = this->pointsFrom[srcObj].begin(); it != this->pointsFrom[srcObj].end(); ) {
                ObjectPointsTo *p = *it;
                if (p->fieldId == pto->fieldId && p->dstfieldId == pto->dstfieldId) {
                    if (act < 0) {
                        it = this->pointsFrom[srcObj].erase(it);
                    }else {
                        //Just deactivate the pointsFrom record w/o removing it.
                        p->is_active = !!act;
                        ++it;
                    }
                }else {
                    ++it;
                }
            }
            return true;
        }

        //activate/de-activate the field pto record.
        void activateFieldPto(ObjectPointsTo *pto, bool activate = true) {
            if (!pto) {
                return;
            }
            if (activate) {
                pto->is_active = true;
                if (pto->targetObject) {
                    pto->targetObject->erasePointsFrom(this,pto,1);
                }
            }else {
                pto->is_active = false;
                if (pto->targetObject) {
                    pto->targetObject->erasePointsFrom(this,pto,0);
                }
            }
            return;
        }

        //Get the type of a specific field in this object.
        Type *getFieldTy(long fid, int *err = nullptr) {
            int r;
            if (!err) 
                err = &r;
            *err = 0;
            if (!this->targetType) {
                *err = 1;
                return nullptr;
            }
            Type *ety = this->targetType;
            if (dyn_cast<CompositeType>(this->targetType)) {
                //Boundary check
                if (!InstructionUtils::isIndexValid(this->targetType,fid)) {
                    *err = 2;
                    return nullptr;
                }
                //TODO: when fid is 0, we're actually not sure whether it points to the host obj itself, or the field 0 in the obj...
                ety = dyn_cast<CompositeType>(this->targetType)->getTypeAtIndex(fid);
            }else if (fid) {
                //This is not a composite obj, so we don't know the field type at the non-zero fid.
                *err = 3;
                return nullptr;
            }
            return ety;
        }

        //Sometimes the field itself can be another embedded struct, this function intends to return all types at a specific field.
        void getNestedFieldTy(long fid, std::set<Type*> &retSet) {
            Type *ety = (fid ? this->getFieldTy(fid) : this->targetType);
            if (ety) {
                FieldDesc *fd = InstructionUtils::getHeadFieldDesc(ety);
                if (fd) {
                    for (Type *t : fd->tys) {
                        retSet.insert(t);
                    }
                }
            }
            return;
        }

        //We want to get all possible pointee types of a certain field, so we need to inspect the detailed type desc (i.e. embed/parent object hierarchy).
        void getFieldPointeeTy(long fid, std::set<Type*> &retSet) {
            if (this->pointsTo.find(fid) == this->pointsTo.end()) {
                return;
            }
            for (ObjectPointsTo *obj : this->pointsTo[fid]) {
                if (obj->fieldId == fid) {
                    if (!obj->targetObject) {
                        continue;
                    }
                    obj->targetObject->getNestedFieldTy(obj->dstfieldId,retSet);
                }
            }
            return;
        }

        //This is a wrapper of "updateFieldPointsTo" for convenience, it assumes that we only have one pto record for the "fieldId" to update,
        //and this pto points to field 0 of "dstObject".
        //NOTE: currently this is only invoked in the initial global object setup phase (e.g. need to make gv0->f0 point to gv1)
        //TODO: consider to replace more "updateFieldPointsTo" invocation to this when applicable, to simplify the codebase.
        void addObjectToFieldPointsTo(long fieldId, AliasObject *dstObject, InstLoc *propagatingInstr = nullptr, bool is_weak = false) {
#ifdef DEBUG_UPDATE_FIELD_POINT
            dbgs() << "addObjectToFieldPointsTo() for: " << InstructionUtils::getTypeStr(this->targetType) << " | " << fieldId;
            dbgs() << " Host Obj ID: " << (const void*)this << "\n";
#endif
            if(dstObject != nullptr) {
                std::set<PointerPointsTo*> dstPointsTo;
                PointerPointsTo *newPointsTo = new PointerPointsTo(nullptr,fieldId,dstObject,0,propagatingInstr,is_weak);
                dstPointsTo.insert(newPointsTo);
                this->updateFieldPointsTo(fieldId,&dstPointsTo,propagatingInstr);
                //We can now delete the allocated objects since "updateFieldPointsTo" has made a copy.
                delete(newPointsTo);
            }
        }

        bool getPossibleMemberFunctions_dbg(Instruction *inst, FunctionType *targetFunctionType, Type *host_ty, long field, std::vector<Function *> &targetFunctions) {
            if (!inst || !targetFunctionType || !host_ty || field < 0 || field >= host_ty->getStructNumElements()) {
                return false;
            }
            Module *currModule = inst->getParent()->getParent()->getParent();
            for(auto a = currModule->begin(), b = currModule->end(); a != b; a++) {
                Function *currFunction = &(*a);
                if(!currFunction->isDeclaration()) {
                    if (currFunction->getName().str() != "vt_ioctl") {
                        continue;
                    }
                    dbgs() << "Find vt_ioctl()\n";
                    std::map<ConstantAggregate*,std::set<long>> *res = InstructionUtils::getUsesInStruct(currFunction);
                    if (res) {
                        dbgs() << "getUsesInStruct succeed!\n";
                        for (auto& x : *res) {
                            dbgs() << "-------------------\n";
                            dbgs() << InstructionUtils::getValueStr(x.first) << "\n";
                            for (auto &y : x.second) {
                                dbgs() << y << ", ";
                            }
                            dbgs() << "\n";
                        }
                    }
                    for (Value::user_iterator i = currFunction->user_begin(), e = currFunction->user_end(); i != e; ++i) {
                        ConstantExpr *constExp = dyn_cast<ConstantExpr>(*i);
                        ConstantAggregate *currConstA = dyn_cast<ConstantAggregate>(*i);
                        GlobalValue *currGV = dyn_cast<GlobalValue>(*i);
                        dbgs() << "USE: " << InstructionUtils::getValueStr(*i) << "### " << (constExp!=nullptr) << "|" << (currConstA!=nullptr) << "|" << (currGV!=nullptr) << "\n";
                        if(constExp != nullptr) {
                            for (Value::user_iterator j = constExp->user_begin(), je = constExp->user_end(); j != je; ++j) {
                                ConstantAggregate *currConstAC = dyn_cast<ConstantAggregate>(*j);
                                dbgs() << "USE(CEXPR): " << InstructionUtils::getValueStr(*i) << "### " << (currConstAC!=nullptr) << "\n";
                            }
                        }
                        if(currConstA != nullptr) {
                            dbgs() << "Find its use as a ConstantAggregate:\n";
                            dbgs() << InstructionUtils::getValueStr(currConstA) << "\n";
                            Constant *constF = currConstA->getAggregateElement(12);
                            if (!constF) {
                                dbgs() << "Failure currConstA->getAggregateElement(12)\n";
                                continue;
                            }
                            dbgs() << "constF: " << InstructionUtils::getValueStr(constF) << "\n";
                            Function *dstFunc = dyn_cast<Function>(constF);
                            if (!dstFunc && dyn_cast<ConstantExpr>(constF)) {
                                dbgs() << "!dstFunc && dyn_cast<ConstantExpr>(constF)\n";
                                //Maybe this field is a casted function pointer.
                                ConstantExpr *constE = dyn_cast<ConstantExpr>(constF);
                                if (constE->isCast()) {
                                    dbgs() << "constE->isCast()\n";
                                    Value *op = constE->getOperand(0);
                                    dstFunc = dyn_cast<Function>(op);
                                    //dstFunc might still be null.
                                }
                            }
                            if (dstFunc) {
                                dbgs() << dstFunc->getName().str() << "\n";
                            }else {
                                dbgs() << "Null dstFunc\n";
                            }
                        }
                    }
                }
            }
            return false;
        }

        //Try to find a proper function for a func pointer field in a struct.
        bool getPossibleMemberFunctions(Instruction *inst, FunctionType *targetFunctionType, Type *host_ty, long field, std::vector<Function *> &targetFunctions) {
            if (!inst || !targetFunctionType || !host_ty || !dyn_cast<CompositeType>(host_ty)) {
                return false;
            }
            if (field < 0 || !InstructionUtils::isIndexValid(host_ty,(unsigned)field)) {
                return false;
            }
#ifdef DEBUG_SMART_FUNCTION_PTR_RESOLVE
            dbgs() << "getPossibleMemberFunctions: inst: ";
            dbgs() << InstructionUtils::getValueStr(inst) << "\n";
            dbgs() << "FUNC: " << InstructionUtils::getTypeStr(targetFunctionType);
            dbgs() << " STRUCT: " << InstructionUtils::getTypeStr(host_ty) << " | " << field << "\n";
#endif
            Module *currModule = inst->getParent()->getParent()->getParent();
            for(auto a = currModule->begin(), b = currModule->end(); a != b; a++) {
                Function *currFunction = &(*a);
                // does the current function has same type of the call instruction?
                if(!currFunction->isDeclaration() && InstructionUtils::same_types(currFunction->getFunctionType(), targetFunctionType)) {
#ifdef DEBUG_SMART_FUNCTION_PTR_RESOLVE
                    dbgs() << "getPossibleMemberFunctions: Got a same-typed candidate callee: ";
                    dbgs() << currFunction->getName().str() << "\n";
#endif
                    //Our filter logic is that the candidate function should appear in a constant (global) struct as a field,
                    //with the struct type "host_ty" and fieldID "field".
                    std::map<ConstantAggregate*,std::set<long>> *res = InstructionUtils::getUsesInStruct(currFunction);
                    if (!res || res->empty()) {
                        continue;
                    }
                    for (auto& x : *res) {
#ifdef DEBUG_SMART_FUNCTION_PTR_RESOLVE
                        dbgs() << "USE: STRUCT: " << InstructionUtils::getTypeStr((x.first)->getType()) << " #";
                        for (auto& y : x.second) {
                            dbgs() << y << ", ";
                        }
                        dbgs() << "\n";
#endif
                        if (InstructionUtils::same_types((x.first)->getType(), host_ty)) {
                            if (dyn_cast<StructType>(host_ty)) {
                                //field-sensitive for the struct.
                                if (x.second.find(field) != x.second.end()) {
#ifdef DEBUG_SMART_FUNCTION_PTR_RESOLVE
                                    dbgs() << "getPossibleMemberFunctions: add to final list (struct).\n";
#endif
                                    targetFunctions.push_back(currFunction);
                                    break;
                                }
                            }else if (dyn_cast<SequentialType>(host_ty)) {
                                //Since we now collapse an array to one element, we need to return func pointers for all fields..
#ifdef DEBUG_SMART_FUNCTION_PTR_RESOLVE
                                dbgs() << "getPossibleMemberFunctions: add to final list (sequential).\n";
#endif
                                targetFunctions.push_back(currFunction);
                                break;
                            }else {
                                //Impossible.
                                assert("Unrecognized CompositeType" && false);
                            }
                        }
                    }
                }
            }

            // Find only those functions which are part of the driver.
            DILocation *instrLoc = nullptr;
            instrLoc = inst->getDebugLoc().get();
            if(instrLoc != nullptr) {
                std::string currFileName = instrLoc->getFilename();
                size_t found = currFileName.find_last_of("/");
                std::string parFol = currFileName.substr(0, found);
                std::vector<Function *> newList;
                for(auto cf:targetFunctions) {
                    instrLoc = cf->getEntryBlock().getFirstNonPHIOrDbg()->getDebugLoc().get();
                    if(instrLoc != nullptr) {
                        currFileName = instrLoc->getFilename();
                        if(currFileName.find(parFol) != std::string::npos) {
                            newList.push_back(cf);
                        }
                    }
                }
                targetFunctions.clear();
                targetFunctions.insert(targetFunctions.end(), newList.begin(), newList.end());

            } else {
                targetFunctions.clear();
            }

            return targetFunctions.size() > 0;
        }

        //TaintInfo helpers start

        /***
         * Get the set of taint flag of the provided field.
         * @param srcfieldId field id for which taint need to be fetched.
         * @return set of taint flags.
         */
        std::set<TaintFlag*> *getFieldTaintInfo(long srcfieldId) {
            FieldTaint *targetFieldTaint = this->getFieldTaint(srcfieldId);
            if(targetFieldTaint != nullptr) {
                return &(targetFieldTaint->targetTaint);
            } else {
                if (this->all_contents_taint_flag) {
                    this->addFieldTaintFlag(srcfieldId, this->all_contents_taint_flag);
                    // This cannot be null because we have just added it.
                    return &(this->getFieldTaint(srcfieldId)->targetTaint);
                }
            }
            return nullptr;
        }

        /***
         * Add provided taint flag to the object at the provided field.
         * @param srcfieldId field to which taint needs to be added.
         * @param targetTaintFlag TaintFlag which needs to be added to the
         *                         provided field.
         * @return true if added else false if the taint flag is a duplicate.
         */
        bool addFieldTaintFlag(long srcfieldId, TaintFlag *targetTaintFlag) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
            dbgs() << "AliasObject::addFieldTaintFlag(): " << InstructionUtils::getTypeStr(this->targetType) << " | " << srcfieldId << " obj: " << (const void*)this << "\n";
#endif
            FieldTaint *targetFieldTaint = this->getFieldTaint(srcfieldId);
            if(targetFieldTaint == nullptr) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
                dbgs() << "AliasObject::addFieldTaintFlag(): No field taint exists for this field.\n";
#endif
                targetFieldTaint = new FieldTaint(srcfieldId);
                this->taintedFields.push_back(targetFieldTaint);
            }
            if (targetFieldTaint->addTaintFlag(targetTaintFlag)) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
                if (targetTaintFlag->tag) {
                    dbgs() << "++++TAG: ";
                    targetTaintFlag->tag->dumpInfo_light(dbgs());
                }
#endif
                return true;
            }
            return false;
        }

        /***
         * Add provided taint to all the fields of this object.
         * @param targetTaintFlag TaintFlag that need to be added to all the fields.
         *
         * @return true if added else false if the taint flag is a duplicate.
         */
        bool taintAllFields(TaintFlag *targetTaintFlag) {
            if(!this->all_contents_tainted) {
                this->all_contents_tainted = true;
                this->all_contents_taint_flag = targetTaintFlag;
                std::set<long> allAvailableFields = getAllAvailableFields();

                // add the taint to all available fields.
                for (auto fieldId:allAvailableFields) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
                    dbgs() << "AliasObject::taintAllFields(): Adding taint to field:" << fieldId << "\n";
#endif
                    addFieldTaintFlag(fieldId, targetTaintFlag);
                }

                return true;
            }
            return false;

        }

        inline Value *getValue();

        inline void setValue(Value*);

        virtual void taintSubObj(AliasObject *newObj, long srcfieldId, InstLoc *targetInstr);

        virtual void fetchPointsToObjects(long srcfieldId, std::set<std::pair<long, AliasObject*>> &dstObjects,
            InstLoc *currInst = nullptr, bool create_arg_obj = false);

        virtual void fetchPointsToObjects_log(long srcfieldId, std::set<std::pair<long, AliasObject*>> &dstObjects,
            Instruction *targetInstr, bool create_arg_obj);

        //Get the living field ptos at a certain InstLoc.
        virtual void getLivePtos(long fid, InstLoc *loc, std::set<ObjectPointsTo*> *retPto);

        //Reset the field pto records when switching to a new entry function.
        virtual void resetPtos(long fid, Instruction *entry);

        //Decide whether the "p" may point to this AliasObject.
        //Return: negative: impossible, positive: the larger, the more likely.
        virtual int maybeAPointee(Value *p);

        //hz: taint all fields and attach a different taint tag for each field in the TaintFlag.
        bool taintAllFieldsWithTag(TaintFlag *targetTaintFlag) {
            Value *v = this->getValue();
            if (v == nullptr && this->targetType == nullptr){
#ifdef DEBUG_UPDATE_FIELD_TAINT
                dbgs() << "AliasObject::taintAllFieldsWithTag(): Neither Value nor Type information available for obj: " << (const void*)this << "\n";
#endif
                return false;
            }
            assert(targetTaintFlag);
            if(!this->all_contents_tainted) {
                TaintTag *existingTag = targetTaintFlag->tag;
                bool is_global = true;
                if (existingTag && !existingTag->is_global) {
                    is_global = false;
                }
                this->all_contents_tainted = true;
                //"0" represents that we are not referring to a certain field.
                TaintTag *all_taint_tag = nullptr;
                if (v) {
                    all_taint_tag = new TaintTag(0,v,is_global,(void*)this);
                }else {
                    all_taint_tag = new TaintTag(0,this->targetType,is_global,(void*)this);
                }
                this->all_contents_taint_flag = new TaintFlag(targetTaintFlag,all_taint_tag);
                this->all_contents_taint_flag->is_inherent = true;
                std::set<long> allAvailableFields = getAllAvailableFields();

                // add the taint to all available fields.
#ifdef DEBUG_UPDATE_FIELD_TAINT
                dbgs() << "AliasObject::taintAllFieldsWithTag(): Updating field taint for obj: " << (const void*)this << "\n";
#endif
                for (auto fieldId:allAvailableFields) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
                    dbgs() << "AliasObject::taintAllFieldsWithTag(): Adding taint to field:" << fieldId << "\n";
#endif
                    TaintTag *tag = nullptr;
                    if (v) {
                        tag = new TaintTag(fieldId,v,is_global,(void*)this);
                    }else {
                        tag = new TaintTag(fieldId,this->targetType,is_global,(void*)this);
                    }
                    TaintFlag *newFlag = new TaintFlag(targetTaintFlag,tag);
                    newFlag->is_inherent = true;
                    addFieldTaintFlag(fieldId, newFlag);
                }

                return true;
            }
            return false;

        }

        //In some situations we need to reset this AliasObject, e.g. the obj is originally allocated by kmalloc() w/ a type i8*, and then converted to a composite type.
        //NOTE: after invoking this we usually need to re-taint the changed object.
        void reset(Value *v, Type *ty) {
            this->setValue(v);
            if (v && v->getType() && !ty) {
                ty = v->getType();
                if (ty->isPointerTy()) {
                    ty = ty->getPointerElementType();
                }
            }
            this->targetType = ty;
            this->all_contents_tainted = false;
            delete this->all_contents_taint_flag;
            //TODO: whether need to clear the old field taints...
        }

        std::set<long> getAllAvailableFields() {
            std::set<long> allAvailableFields;
            Type *ty = this->targetType;
            if (ty) {
                if (ty->isPointerTy()) {
                    ty = ty->getPointerElementType();
                }
                if (ty->isStructTy()) {
                    for (long i = 0; i < ty->getStructNumElements(); ++i) {
                        allAvailableFields.insert(i);
                    }
                    return allAvailableFields;
                }else if (dyn_cast<SequentialType>(ty)) {
                    for (long i = 0; i < dyn_cast<SequentialType>(ty)->getNumElements(); ++i) {
                        allAvailableFields.insert(i);
                    }
                    return allAvailableFields;
                }
            }
            if (this->pointsTo.size()) {
                // has some points to?
                // iterate thru pointsTo and get all fields.
                for (auto &x : this->pointsTo) {
                    if (x.second.size()) {
                        allAvailableFields.insert(x.first);
                    }
                }
            }else {
                // This must be a scalar type, or null type info.
                // just add taint to the field 0.
                allAvailableFields.insert(0);
            }
            return allAvailableFields;
        }

        //TaintInfo helpers end

        //We just created a new pointee object for a certain field in this host object, at this point
        //we may still need to handle some special cases, e.g.
        //(0) This host object A is a "list_head" (i.e. a kernel linked list node) and we created a new "list_head" B pointed to by
        //the A->next, in this case we also need to set B->prev to A.
        //(1) TODO: handle more special cases.
        int handleSpecialFieldPointTo(AliasObject *pobj, long fid, InstLoc *targetInstr) {
            if (!pobj) {
                return 0;
            }
            Type *ht = this->targetType;
            Type *pt = pobj->targetType;
            if (!ht || !pt || !ht->isStructTy() || !pt->isStructTy() || !InstructionUtils::same_types(ht,pt)) {
#ifdef DEBUG_SPECIAL_FIELD_POINTTO
                dbgs() << "AliasObject::handleSpecialFieldPointTo(): ht and pt are not the same struct pointer.\n";
#endif
                return 0;
            }
            //Is it of the type "list_head"?
            std::string ty_name = ht->getStructName().str();
#ifdef DEBUG_SPECIAL_FIELD_POINTTO
            dbgs() << "AliasObject::handleSpecialFieldPointTo(): type name: " << ty_name << "\n";
#endif
            if (ty_name.find("struct.list_head") == 0 && fid >= 0 && fid <= 1) {
#ifdef DEBUG_SPECIAL_FIELD_POINTTO
                dbgs() << "AliasObject::handleSpecialFieldPointTo(): Handle the list_head case: set the prev and next properly..\n";
                dbgs() << "AliasObject::handleSpecialFieldPointTo(): hobj: " << (const void*)this << " pobj: " << (const void*)pobj << " fid: " << fid << "\n";
#endif
                pobj->addObjectToFieldPointsTo(1-fid,this,targetInstr,false);
                return 1;
            }
            return 0;
        }

        virtual AliasObject* makeCopy() {
            return new AliasObject(this);
        }

        virtual Value* getObjectPtr() {
            return nullptr;
        }

        virtual void setObjectPtr(Value *v) {
            return;
        }

        virtual bool isSameObject(AliasObject *other) {
            return this == other;
        }

        virtual Value* getAllocSize() {
            return nullptr;
        }

        virtual int64_t getTypeAllocSize(DataLayout *targetDL) {
            // if there is no type or this is a void*, then we do not know the alloc size.
            if(targetType == nullptr ||
                    (targetType->isPointerTy() &&
                                         targetType->getContainedType(0)->isIntegerTy(8)) ||
                    (!targetType->isSized())) {
                return -1;
            }
            return targetDL->getTypeAllocSize(targetType);
        }

        friend llvm::raw_ostream& operator<<(llvm::raw_ostream& os, const AliasObject& obj) {
            os << "Object with type:";
            obj.targetType->print(os);
            os <<" ID:" << &(obj) << "\n";
            obj.printPointsTo(os);
            return os;
        }

        virtual bool isFunctionArg() {
            /***
             * checks whether the current object is a function argument.
             */
            return false;
        }

        virtual bool isFunctionLocal() {
            /***
             * checks whether the current object is a function local object.
             */
            return false;
        }

        virtual bool isHeapObject() {
            /***
             * Returns True if this object is a malloced Heap object.
             */
            return false;
        }

        virtual bool isHeapLocation() {
            /***
             * Returns True if this object is a HeapLocation instance.
             */
            return false;
        }

        virtual bool isGlobalObject() {
            /***
             * Returns True if this object is a Global object.
             */
            return false;
        }

        //hz: add for new subclass.
        virtual bool isOutsideObject() {
            /***
             * Returns True if this object is an Outside object.
             */
            return false;
        }

        virtual long getArraySize() {
            /***
             *  Returns array size, if this is array object.
             *  else returns -1
             */
             if(this->targetType != nullptr && this->targetType->isArrayTy()) {
                 return this->targetType->getArrayNumElements();
             }
            return -1;
        }

        //NOTE: "is_weak" by default is "-1", this means whether it's a weak update is decided by "is_weak" field of each PointerPointsTo in "dstPointsTo",
        //in some cases, the arg "is_weak" can be set to 0 (strong update) or 1 (weak update) to override the "is_weak" field in "dstPointsTo".
        //NOTE: this function will make a copy of "dstPointsTo" and will not do any modifications to "dstPointsTo", the caller is responsible to free
        //"dstPointsTo" if necessary.
        void updateFieldPointsTo(long srcfieldId, std::set<PointerPointsTo*>* dstPointsTo, InstLoc *propogatingInstr, int is_weak = -1);

        FieldTaint* getFieldTaint(long srcfieldId) {
            for(auto currFieldTaint : taintedFields) {
                if(currFieldTaint->fieldId == srcfieldId) {
                    return currFieldTaint;
                }
            }
            return nullptr;
        }

    private:

        //NOTE: the arg "is_weak" has the same usage as updateFieldPointsTo().
        void updateFieldPointsTo_do(long srcfieldId, std::set<PointerPointsTo*>* dstPointsTo, InstLoc *propogatingInstr, int is_weak = -1);

    protected:
        void printPointsTo(llvm::raw_ostream& os) const {
            os << "Points To Information:\n";
            for (auto &x : this->pointsTo) {
                os << "Field: " << x.first << ":\n";
                for (ObjectPointsTo *obp : x.second) {
                    os << "\t" << (*obp) << "\n";
                }
            }
        }
    };

    class FunctionLocalVariable : public AliasObject {
    public:
        Function *targetFunction;
        Value *targetAllocaInst;
        Value *targetVar;
        // This differentiates local variables from different calling context.
        std::vector<Instruction *> *callSiteContext;

        FunctionLocalVariable(AllocaInst &targetInst, std::vector<Instruction *> *callSites) {
            this->targetFunction = targetInst.getFunction();
            this->targetType = targetInst.getAllocatedType();
            this->targetAllocaInst = &targetInst;
            this->callSiteContext = callSites;
            // get the local variable to which this is allocated.
            this->targetVar = &targetInst;
            if(targetInst.getAllocatedType()->isStructTy()) {
                this->is_initialized = false;
                this->initializingInstructions.clear();
            }
        }

        FunctionLocalVariable(FunctionLocalVariable *srcLocalVariable): AliasObject(srcLocalVariable) {
            this->targetFunction = srcLocalVariable->targetFunction;
            this->targetAllocaInst = srcLocalVariable->targetAllocaInst;
            this->targetVar = srcLocalVariable->targetVar;
            this->callSiteContext = srcLocalVariable->callSiteContext;
            this->targetType = srcLocalVariable->targetType;
        }

        AliasObject* makeCopy() {
            return new FunctionLocalVariable(this);
        }

        Value* getObjectPtr() {
            return this->targetAllocaInst;
        }

        void setObjectPtr(Value *v) {
            this->targetAllocaInst = v;
        }

        bool isFunctionLocal() {
            return true;
        }

        friend llvm::raw_ostream& operator<<(llvm::raw_ostream& os, const FunctionLocalVariable& obj) {
            os << "Function Local variable with type:";
            obj.targetType->print(os);
            os <<" ID:" << obj.id << "\n";
            obj.printPointsTo(os);
            return os;
        }


    };

    class GlobalObject : public AliasObject {
    public:
        Value *targetVar;
        GlobalObject(llvm::GlobalVariable *globalDef, Type *globVarType) {
            this->targetVar = (Value*)globalDef;
            this->targetType = globVarType;
        }
        GlobalObject(Value* globalVal, Type *globVarType) {
            this->targetVar = globalVal;
            this->targetType = globVarType;
        }
        GlobalObject(Function *targetFunction) {
            this->targetVar = targetFunction;
            this->targetType = targetFunction->getType();
        }
        GlobalObject(GlobalObject *origGlobVar): AliasObject(origGlobVar) {
            this->targetVar = origGlobVar->targetVar;
            this->targetType = origGlobVar->targetType;
        }
        AliasObject* makeCopy() {
            return new GlobalObject(this);
        }
        Value* getObjectPtr() {
            return this->targetVar;
        }

        void setObjectPtr(Value *v) {
            this->targetVar = v;
        }

        bool isGlobalObject() {
            return true;
        }
    };

    //hz: create a new GlobalObject for a pointer Value w/o point-to information, this
    //can be used for driver function argument like FILE * which is defined outside the driver module.
    class OutsideObject : public AliasObject {
    public:
        //hz: the pointer to the outside object.
        Value *targetVar;
        OutsideObject(Value* outVal, Type *outVarType) {
            this->targetVar = outVal;
            this->targetType = outVarType;
#ifdef DEBUG_OUTSIDE_OBJ_CREATION
            dbgs() << "###NEW OutsideObj: targetVar: " << InstructionUtils::getValueStr(this->targetVar) << " ty: " << InstructionUtils::getTypeStr(this->targetType) << "\n";
#endif
        }
        OutsideObject(OutsideObject *origOutsideVar): AliasObject(origOutsideVar) {
            this->targetVar = origOutsideVar->targetVar;
            this->targetType = origOutsideVar->targetType;
#ifdef DEBUG_OUTSIDE_OBJ_CREATION
            dbgs() << "###COPY OutsideObj: targetVar: " << InstructionUtils::getValueStr(this->targetVar) << " ty: " << InstructionUtils::getTypeStr(this->targetType) << "\n";
#endif
        }
        AliasObject* makeCopy() {
            return new OutsideObject(this);
        }

        Value* getObjectPtr() {
            return this->targetVar;
        }

        void setObjectPtr(Value *v) {
            this->targetVar = v;
        }

        bool isOutsideObject() {
            return true;
        }

    };

    class HeapLocation : public AliasObject {
    public:
        Function *targetFunction;
        Value *targetAllocInstruction;
        std::vector<Instruction *> *callSiteContext;
        Value *targetAllocSize;
        bool is_malloced;

        HeapLocation(Instruction &allocSite, Type* targetType, std::vector<Instruction *> *callSites,
                     Value *allocSize, bool is_malloced) {
            this->targetType = targetType;
            this->targetAllocInstruction = &allocSite;
            this->targetFunction = allocSite.getParent()->getParent();
            this->callSiteContext = callSites;
            this->targetAllocSize = allocSize;
            this->is_malloced = is_malloced;
            this->is_initialized = false;
            this->initializingInstructions.clear();
        }
        HeapLocation(HeapLocation *srcHeapLocation): AliasObject(srcHeapLocation) {
            this->targetAllocInstruction = srcHeapLocation->targetAllocInstruction;
            this->targetFunction = srcHeapLocation->targetFunction;
            this->targetType = srcHeapLocation->targetType;
            this->callSiteContext = srcHeapLocation->callSiteContext;
            this->targetAllocSize = srcHeapLocation->targetAllocSize;
            this->is_malloced = srcHeapLocation->is_malloced;
        }
        AliasObject* makeCopy() {
            return new HeapLocation(this);
        }
        Value* getObjectPtr() {
            return this->targetAllocInstruction;
        }

        void setObjectPtr(Value *v) {
            this->targetAllocInstruction = v;
        }

        Value* getAllocSize() {
            return targetAllocSize;
        }

        bool isHeapObject() {
            /***
             * Return true if this is malloced
             */
            return this->is_malloced;
        }

        bool isHeapLocation() {
            return true;
        }

    };

    class FunctionArgument : public AliasObject {
    public:
        std::vector<Instruction *> *callSiteContext;
        Function *targetFunction;
        Value *targetArgument;
        // TODO: handle pointer args
        FunctionArgument(Value *targetArgument, Type* targetType, Function *tarFunction, std::vector<Instruction *> *callSites) {
            this->targetType = targetType;
            this->targetFunction = tarFunction;
            this->targetArgument = targetArgument;
            this->callSiteContext = callSites;
        }
        FunctionArgument(FunctionArgument *srcFunctionArg) : AliasObject(srcFunctionArg) {
            this->targetFunction = srcFunctionArg->targetFunction;
            this->targetArgument = srcFunctionArg->targetArgument;
            this->callSiteContext = srcFunctionArg->callSiteContext;
            this->targetType = srcFunctionArg->targetType;
        }

        AliasObject* makeCopy() {
            return new FunctionArgument(this);
        }

        Value* getObjectPtr() {
            return this->targetArgument;
        }

        void setObjectPtr(Value *v) {
            this->targetArgument = v;
        }

        bool isFunctionArg() {
            return true;
        }
    };

    //hz: get the llvm::Value behind this AliasObject.
    Value *AliasObject::getValue() {
        return this->getObjectPtr();
        /*
        Value *v = nullptr;
        if (this->isGlobalObject()){
            v = ((DRCHECKER::GlobalObject*)this)->targetVar;
        }else if(this->isFunctionArg()){
            v = ((DRCHECKER::FunctionArgument*)this)->targetArgument;
        }else if (this->isFunctionLocal()){
            v = ((DRCHECKER::FunctionLocalVariable*)this)->targetVar;
        }else if (this->isOutsideObject()){
            v = ((DRCHECKER::OutsideObject*)this)->targetVar;
        }//TODO: HeapAllocation
        return v;
        */
    }

    void AliasObject::setValue(Value *v) {
        this->setObjectPtr(v);
    }

    //hz: A helper method to create and (taint) a new OutsideObject according to a given type.
    //Note that all we need is the type, in the program there may not exist any IR that can actually point to the newly created object,
    //thus this method is basically for the internal use (e.g. in multi-dimension GEP, or in fetchPointToObjects()).
    extern OutsideObject* createOutsideObj(Type *ty, bool taint, std::set<TaintFlag*> *existingTaints);

    extern int updatePointsToRecord(InstLoc *vloc, std::map<Value*,std::set<PointerPointsTo*>*> *currPointsTo, AliasObject *newObj, long fid = 0, long dfid = 0);

    //hz: A helper method to create and (taint) a new OutsideObject according to a given pointer value (possibly an IR).
    //The arg "currPointsTo" is the current global point-to state.
    extern OutsideObject* createOutsideObj(InstLoc *vloc, std::map<Value*,std::set<PointerPointsTo*>*> *currPointsTo, bool taint, std::set<TaintFlag*> *existingTaints);

    //hz: A helper method to create and (taint) an embedded struct obj in the host obj.
    //The arg "currPointsTo" is the current global point-to state.
    extern AliasObject *createEmbObj(AliasObject *hostObj, long host_dstFieldId, InstLoc *vloc = nullptr, std::map<Value*, std::set<PointerPointsTo*>*> *currPointsTo = nullptr);

    //Given a embedded object and its #field within the host object, and the host type, create the host object
    //and maintain their embedding relationships preperly.
    extern AliasObject *createHostObj(AliasObject *targetObj, Type *hostTy, long field);

    extern int matchFieldsInDesc(Module *mod, Type *ty0, std::string& n0, Type *ty1, std::string& n1, int bitoff, std::vector<FieldDesc*> *fds, std::vector<unsigned> *res);

    extern void sortCandStruct(std::vector<CandStructInf*> *cands, std::set<Instruction*> *insts);

    //Given 2 field types and their distance (in bits), return a list of candidate struct types.
    extern std::vector<CandStructInf*> *getStructFrom2Fields(DataLayout *dl, Type *ty0, std::string& n0, Type *ty1, std::string& n1, long bitoff, Module *mod);

    //This function assumes that "v" is a i8* srcPointer of a single-index GEP and it points to the "bitoff" inside an object of "ty",
    //our goal is to find out the possible container objects of the target object of "ty" (the single-index GEP aims to locate a field
    //that is possibly outside the scope of current "ty" so we need to know the container), to do this we will analyze all similar GEPs
    //that use the same "v" as the srcPointer.
    //Return: we return a "CandStructInf" to indicate the location of the original "bitoff" inside "ty" in the larger container object.
    extern CandStructInf *inferContainerTy(Module *m,Value *v,Type *ty,long bitoff);

    //hz: when analyzing multiple entry functions, they may share some objects:
    //(0) explicit global objects, we don't need to take special care of these objects since they are pre-created before all analysis and will naturally shared.
    //(1) the outside objects created by us on the fly (e.g. the file->private in the driver), multiple entry functions in driver (e.g. .ioctl and .read/.write)
    //can shared the same outside objects, so we design this obj cache to record all the top-level outside objects created when analyzing each entry function,
    //when we need to create a same type outside object later in a different entry function, we will then directly retrieve it from this cache.
    //TODO: what about the kmalloc'ed objects whose types are later changed to a struct...
    extern std::map<Type*,std::map<Function*,std::set<OutsideObject*>>> sharedObjCache;

    extern Function *currEntryFunc;

    extern int addToSharedObjCache(OutsideObject *obj);

    extern OutsideObject *getSharedObjFromCache(Value *v,Type *ty);

    //"fd" is a bit offset desc of "pto->targetObject", it can reside in nested composite fields, this function creates all nested composite fields
    //in order to access the bit offset of "fd", while "limit" is the lowest index we try to create an emb obj in fd->host_tys[].
    extern int createEmbObjChain(FieldDesc *fd, PointerPointsTo *pto, int limit);

    extern int createHostObjChain(FieldDesc *fd, PointerPointsTo *pto, int limit);

}

#endif //PROJECT_ALIASOBJECT_H
