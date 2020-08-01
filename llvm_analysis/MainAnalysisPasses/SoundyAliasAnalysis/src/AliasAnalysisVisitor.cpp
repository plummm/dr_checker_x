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
#define DEBUG_LOAD_INSTR
#define DEBUG_STORE_INSTR
//#define DEBUG_CALL_INSTR
//#define STRICT_CAST
//#define DEBUG_RET_INSTR
//#define FAST_HEURISTIC
//#define MAX_ALIAS_OBJ 50
//hz: Enable creating new outside objects on the fly when the pointer points to nothing.
#define CREATE_DUMMY_OBJ_IF_NULL
#define DEBUG_CREATE_DUMMY_OBJ
#define DEBUG_UPDATE_POINTSTO
//#define AGGRESSIVE_PTO_DUP_FILTER
//#define DEBUG_TMP
//#define INFER_XENTRY_SHARED_OBJ

    //hz: A helper method to create and (taint) a new OutsideObject.
    //"p" is the pointer for which we need to create the object, "I" is the instruction as a creation site.
    OutsideObject* AliasAnalysisVisitor::createOutsideObj(Value *p, Instruction *I, bool taint) {
        if (!p) {
            return nullptr;
        }
        if (dyn_cast<GlobalVariable>(p)) {
            //We have already set up all the global pto relationship before all analysis begin, so if now we cannot
            //find the pointee of a certain global variable, that must be we have decided that there is no need to
            //create a pointee object for it (e.g. the gv is a constant string pointer). So we will not create
            //an OutsideObject for it either.
#ifdef DEBUG_CREATE_DUMMY_OBJ
            dbgs() << "AliasAnalysisVisitor::createOutsideObj(): we will not create dummy object for the global variable: "
            << InstructionUtils::getValueStr(p) << "\n";
#endif
            return nullptr;
        }
        InstLoc *loc = nullptr;
        if (I) {
            loc = new InstLoc(I,this->currFuncCallSites);
        }else {
            loc = new InstLoc(p,this->currFuncCallSites);
        }
        std::map<Value*, std::set<PointerPointsTo*>*> *currPointsTo = this->currState.getPointsToInfo(this->currFuncCallSites);
#ifdef INFER_XENTRY_SHARED_OBJ
        //Can we get a same-typed object from the global cache (generated when analyzing another entry function)?
        //NOTE: there are multiple places in the code that create a new OutsideObject, but we onlyd do this multi-entry cache mechanism here,
        //because other places create the object that is related to another object (emb/host/field point-to), while we only need to cache the
        //top-level outside obj here (so that other sub obj can be naturally obtained by the field records inside it).
        if (p->getType() && p->getType()->isPointerTy() && dyn_cast<CompositeType>(p->getType()->getPointerElementType())) {
            OutsideObject *obj = DRCHECKER::getSharedObjFromCache(p,p->getType()->getPointerElementType());
            if (obj) {
                //We need to bind the shared object w/ current inst.
                obj->addPointerPointsTo(p,loc);
                this->updatePointsToObjects(p,obj,loc);
                return obj;
            }
        }
#endif
        //Ok, now we need to create a dummy object for the pointer "p"..
        OutsideObject *robj = DRCHECKER::createOutsideObj(p,loc);
        if (robj) {
            //Add it to the global pto record.
            this->updatePointsToObjects(p,robj,loc);
            //Then we should consider whether and how to taint it...
            if (taint) {
                //First set this new obj as a taint source, since it's very likely that this is a shared obj inited in other entry functions.
                //TODO: consider whether it's possible that this obj is a user inited taint source, if so, how to recognize this?
                //TODO: it's strange to consider the taint stuff in the AliasAnalysis.
                robj->setAsTaintSrc(loc,true);
                //Then propagate the taint flags from the pointer "p" to the obj.
                std::set<TaintFlag*> *existingTaints = TaintUtils::getTaintInfo(this->currState,this->currFuncCallSites,p);
                if (existingTaints) {
                    for (TaintFlag *tf : *existingTaints) {
                        if (!tf) {
                            continue;
                        }
                        //TODO: in theory we need to test whether the new taint trace is valid (i.e. reachability), we omit it now since
                        //it's less likely that the taint on the pointer cannot reach its pointee..
                        //NOTE: "is_weak" is inherited.
                        TaintFlag *ntf = new TaintFlag(tf,loc);
                        robj->taintAllFields(ntf);
                    }
                }
            }
#ifdef INFER_XENTRY_SHARED_OBJ
            DRCHECKER::addToSharedObjCache(robj);
#endif
        }else {
#ifdef DEBUG_CREATE_DUMMY_OBJ
            dbgs() << "AliasAnalysisVisitor::createOutsideObj(): failed to create the dummy obj!\n";
#endif
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
            dbgs() << (o0?"t":"f") << (o1?"t":"f") << (o0?(o0->isOutsideObject()?"t":"f"):"n") 
            << (o1?(o1->isOutsideObject()?"t":"f"):"n") << "\n";
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
            dbgs() << "Ptr0: " << InstructionUtils::getValueStr(v0) << " Ptr1: " 
            << InstructionUtils::getValueStr(v1) << " RES: " << (v0==v1?"T":"F") << "\n";
        }
        return (v0 == v1);
#else
        return false;
#endif
    }

    //Basically we try to see whether the pointee object type matches that of srcPointer, if not, we try adjust the PointerPointsTo, e.g.,
    //by walking through the embed/parent hierarchy of the pointee object.
    //"loc" is the instruction site where we need to match the pto.
    //"create_host" indicates whether to automatically create a host object if that's necessary for 
    //a match (i.e. current pto points to a struct that can be embedded in a host object).
    //Return: whether the type is matched in the end.
    int AliasAnalysisVisitor::matchPtoTy(Value *srcPointer, PointerPointsTo *pto, Instruction *I, bool create_host) {
        if (!srcPointer || !pto || !pto->targetObject) {
            return 0;
        }
        Type *srcTy = srcPointer->getType();
        if (!srcTy || !srcTy->isPointerTy()) {
            return 0;
        }
        srcTy = srcTy->getPointerElementType();
        return this->matchPtoTy(srcTy,pto,I,create_host);
    }

    //srcTy is the type we should point to.
    int AliasAnalysisVisitor::matchPtoTy(Type *srcTy, PointerPointsTo *pto, Instruction *I, bool create_host) {
        if (!pto || !pto->targetObject) {
            return 0;
        }
        AliasObject *obj = pto->targetObject;
        Type *pTy = obj->targetType;
        if (!srcTy || !pTy) {
            return 0;
        }
        long dstfieldId = pto->dstfieldId;
        if (InstructionUtils::same_types(obj->getFieldTy(dstfieldId),srcTy)) {
            //Quick path: field match.
            return 1;
        }
        if (dstfieldId == 0 && InstructionUtils::same_types(srcTy,pTy)) {
            //Quick path: direct host match.
            return 2;
        }
        //DataLayout *dl = this->currState.targetDataLayout;
        //Ok, first let's see whether srcTy can match the type of any embedded fields in the pto.
        std::set<Type*> etys;
        obj->getNestedFieldTy(dstfieldId, etys);
        for (Type *ety : etys) {
            if (InstructionUtils::same_types(ety,srcTy)) {
                //Ok, we just need to get/create the proper embedded object and return its pto.
#ifdef DEBUG_UPDATE_POINTSTO
                dbgs() << "AliasAnalysisVisitor::matchPtoTy(): We need to adjust the current pto to an embedded field to match the srcPointer!\n";
#endif
                InstLoc *loc = (I ? new InstLoc(I,this->currFuncCallSites) : nullptr);
                AliasObject *eobj = obj->getNestedObj(dstfieldId,ety,loc);
                if (eobj && eobj != obj && InstructionUtils::same_types(eobj->getFieldTy(0),srcTy)) {
                    pto->targetObject = eobj;
                    pto->dstfieldId = 0;
                    //Matched: emb obj.
                    return 3;
                }
                //Here, (1) "srcTy" cannot directly match the given field type in "pto", 
                //(2) we're sure that it can match one emb obj of the given field,
                //but the thing is we failed to get/create that specific emb obj at the given field w/ "getNestedObj", i
                //though strange, we can do nothing now..
                dbgs() << "!!! AliasAnalysisVisitor::matchPtoTy(): Failed to get/create the emb obj that should be there!\n";
                return 0;
            }
        }
        //Ok, we cannot match the "srcTy" in any layer of embedded objects at the given field, now consider whether
        //we can match any parent object of current "obj".
        if (dstfieldId || !dyn_cast<CompositeType>(srcTy)) {
            return 0;
        }
        //First, is there existing parent object on record that can match "srcTy"?
        while (obj && obj->parent && obj->parent_field == 0) {
            obj = obj->parent;
            pto->targetObject = obj;
            pto->dstfieldId = 0;
            if (InstructionUtils::same_types(srcTy,obj->targetType)) {
                //Got the match!
#ifdef DEBUG_UPDATE_POINTSTO
                dbgs() << "AliasAnalysisVisitor::matchPtoTy(): We need to adjust the current pto to\
                an existing parent object to match the srcPointer!\n";
#endif
                //Matched: host obj.
                return 4;
            }
        }
        //No matching parent objects on file, now consider whether we can create one, according to the given "srcTy".
        if (!create_host) {
            return 0;
        }
#ifdef DEBUG_UPDATE_POINTSTO
        dbgs() << "AliasAnalysisVisitor::matchPtoTy(): try to create a host object to match the srcTy!\n";
#endif
        FieldDesc *fd = InstructionUtils::getHeadFieldDesc(srcTy);
        if (!fd || fd->fid.size() != fd->host_tys.size()) {
#ifdef DEBUG_UPDATE_POINTSTO
            dbgs() << "!!! AliasAnalysisVisitor::matchPtoTy(): failed to get the header FieldDesc of srcTy, or the FieldDesc is invalid!\n";
#endif
            return 0;
        }
        if (fd->findTy(obj->targetType) >= 0) {
            //Ok, the "srcTy" can be a parent type for the "obj", there are two possibilities now:
            //(1) current obj is composite, then we will treat it as an emb obj and recursively create its host objs.
            //(2) it's not composite, then we need to first expand (reset) it to the innermost 
            //emb obj, whose host objs will then be created recursively. 
#ifdef DEBUG_UPDATE_POINTSTO
            dbgs() << "AliasAnalysisVisitor::matchPtoTy(): srcTy is a valid host type of current pointee object, creating the host obj...\n";
#endif
            InstLoc *loc = (I ? new InstLoc(I,this->currFuncCallSites) : nullptr);
            if (!dyn_cast<CompositeType>(obj->targetType)) {
#ifdef DEBUG_UPDATE_POINTSTO
                dbgs() << "AliasAnalysisVisitor::matchPtoTy(): expand the non-composite src obj to the innermost emb obj.\n";
#endif
                //TODO: should we still use the old "value" of the obj?
                obj->reset(obj->getValue(),fd->host_tys[0],loc);
            }
            DRCHECKER::createHostObjChain(fd,pto,fd->fid.size(),loc);
            //Sanity check.
            if (pto->targetObject && pto->dstfieldId == 0 && InstructionUtils::same_types(srcTy,pto->targetObject->targetType)) {
#ifdef DEBUG_UPDATE_POINTSTO
                dbgs() << "AliasAnalysisVisitor::matchPtoTy(): successfully created the required host obj!\n";
#endif
                //Matched: host obj.
                return 4;
            }
        } else if (obj->targetType && obj->targetType->isIntegerTy(8)) {
            //NOTE: if the current obj is of type "i8", we consider it as a wildcard that can match the heading field of any struct.
            //In this case, we will directly reset current obj to an obj of "srcTy". 
            InstLoc *loc = (I ? new InstLoc(I,this->currFuncCallSites) : nullptr);
            obj->reset(obj->getValue(),srcTy,loc);
            //Matched: i8 wildcard.
            return 5;
        }
        return 0;
    }

    void AliasAnalysisVisitor::updatePointsToObjects(Value *p, AliasObject *obj, InstLoc *propInst, long fid, long dfid, bool is_weak) {
        if (!p || !obj) {
            return;
        }
        std::set<PointerPointsTo*> ptos;
        PointerPointsTo *pto = new PointerPointsTo(p,fid,obj,dfid,propInst,is_weak);
        ptos.insert(pto);
        return this->updatePointsToObjects(p,&ptos,false);
    }

    void AliasAnalysisVisitor::updatePointsToObjects(Value *srcPointer, std::set<PointerPointsTo*> *newPointsToInfo, bool free = true) {
        /***
         *  Update the pointsto objects of the srcPointer to newPointstoInfo
         *  At the current instruction.
         *
         *  This also takes care of freeing the elements if they are already present.
         */
#ifdef DEBUG_UPDATE_POINTSTO
        dbgs() << "updatePointsToObjects for : " << InstructionUtils::getValueStr(srcPointer) << "\n";
#endif
        if(!newPointsToInfo || newPointsToInfo->size() == 0){
            //nothing to update.
            return;
        }
        std::map<Value*, std::set<PointerPointsTo*>*> *targetPointsToMap = this->currState.getPointsToInfo(this->currFuncCallSites);
        if (targetPointsToMap->find(srcPointer) == targetPointsToMap->end()) {
            (*targetPointsToMap)[srcPointer] = new std::set<PointerPointsTo*>();
        }
        std::set<PointerPointsTo*>* existingPointsTo = (*targetPointsToMap)[srcPointer];
#ifdef DEBUG_UPDATE_POINTSTO
        dbgs() << "#newPointsToInfo: " << newPointsToInfo->size() << " #existingPointsTo: " << existingPointsTo->size() << "\n";
#endif
        for(PointerPointsTo *currPointsTo : *newPointsToInfo) {
            // Some basic sanity check.
            if (!currPointsTo || !currPointsTo->targetObject) {
                continue;
            }
            // for each points to, see if we already have that information, if yes, ignore it.
            if(std::find_if(existingPointsTo->begin(), existingPointsTo->end(), [currPointsTo,this](const PointerPointsTo *n) {
                return this->isPtoDuplicated(currPointsTo,n,false);
            }) == existingPointsTo->end()) {
                //handle the implicit type cast (i.e. type cast that is not explicitly performed by the 'cast' inst) if any.
                Instruction *propInst = nullptr;
                if (currPointsTo->propagatingInst) {
                    propInst = dyn_cast<Instruction>(currPointsTo->propagatingInst->inst);
                }
                matchPtoTy(srcPointer,currPointsTo,propInst);
#ifdef DEBUG_UPDATE_POINTSTO
                dbgs() << "++ PTO: ";
                currPointsTo->print(dbgs());
#endif
                existingPointsTo->insert(existingPointsTo->end(), currPointsTo);
            } else {
                //delete the points to object, as we already have a similar pointsTo object.
                delete(currPointsTo);
            }
        }
        //Free the memory if required.
        if (free) {
            delete(newPointsToInfo);
        }
#ifdef DEBUG_UPDATE_POINTSTO
        dbgs() << "updatePointsToObjects: #After update: " << existingPointsTo->size() << "\n";
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
        if (is_var_fid) {
            fieldId = -1;
        }
        std::set<PointerPointsTo*>* newPointsToInfo = new std::set<PointerPointsTo*>();
        for (PointerPointsTo *currPointsToObj : *srcPointsTo) {
            AliasObject *hostObj = currPointsToObj->targetObject;
            if (!hostObj) {
                continue;
            }
            long dstField = currPointsToObj->dstfieldId;
            Type *host_type = hostObj->targetType;
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): host_type: " 
            << InstructionUtils::getTypeStr(host_type) << " | " << dstField << "\n";
#endif
            //We must ensure that it points to an embedded composite type in another composite.
            if (!host_type || !dyn_cast<CompositeType>(host_type)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): host_type is not composite!\n";
#endif
                continue;
            }
            //Boundary check for src pto.
            if (!InstructionUtils::isIndexValid(host_type,dstField)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): invalid dstField for the host_type!\n";
#endif
                continue;
            }
            //Get the dst field type (must be composite) in the host obj.
            Type *ety = InstructionUtils::getTypeAtIndex(host_type,dstField);
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): ety: " << InstructionUtils::getTypeStr(ety) <<  " | " << fieldId << "\n";
#endif
            if (!ety || !dyn_cast<CompositeType>(ety)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): ety is not a composite field!\n";
#endif
                continue;
            }
            //Boundary check for dst pto.
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
            AliasObject *newObj = this->createEmbObj(hostObj,dstField,srcPointer,propInstruction);
            if(newObj){
                PointerPointsTo *newPointsToObj = new PointerPointsTo(resPointer,0,newObj,fieldId,
                                                                      new InstLoc(propInstruction,this->currFuncCallSites),false);
                newPointsToInfo->insert(newPointsToInfo->begin(), newPointsToObj);
            }else{
#ifdef DEBUG_GET_ELEMENT_PTR
                errs() << "AliasAnalysisVisitor::makePointsToCopy_emb(): cannot get or create embedded object.\n";
#endif
            }
        }
        return newPointsToInfo;
    }

    AliasObject *AliasAnalysisVisitor::createEmbObj(AliasObject *hostObj, long fid, Value *v, Instruction *I) {
        if (!hostObj) {
            return nullptr;
        }
        InstLoc *loc = nullptr;
        if (I) {
            loc = new InstLoc(I,this->currFuncCallSites);
        }else if (v) {
            loc = new InstLoc(v,this->currFuncCallSites);
        }
        AliasObject *eobj = hostObj->createEmbObj(fid,v,loc);
        if (eobj) {
            //We need to add it to the global pto records..
            if (v) {
                this->updatePointsToObjects(v,eobj,loc);
            }
        }else {
#ifdef DEBUG_CREATE_EMB_OBJ
            dbgs() << "AliasAnalysisVisitor::createEmbObj(): failed to create the emb object!\n";
#endif
        }
        return eobj;
    }

    //NOTE: "is_var_fid" indicates whether the target fieldId is a variable instead of a constant.
    std::set<PointerPointsTo*>* AliasAnalysisVisitor::makePointsToCopy(Instruction *propInstruction, Value *srcPointer,
            std::set<PointerPointsTo*> *srcPointsTo, long fieldId, bool is_var_fid) {
        /***
         * Makes copy of points to information from srcPointer to propInstruction
         */
        if (!srcPointsTo || srcPointsTo->empty()) {
            return nullptr;
        }
        std::set<PointerPointsTo*> *newPointsToInfo = new std::set<PointerPointsTo*>();
        // set of all visited objects to avoid added duplicate pointsto objects.
        std::set<std::pair<long,AliasObject*>> visitedObjects;
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): #elements in *srcPointsTo: " << srcPointsTo->size() << " \n";
#endif
        if (is_var_fid) {
            fieldId = -1;
        }
        //The arg "srcPointer" actually is not related to arg "srcPointsTo", it's indeed "dstPointer" that we need to copy point-to inf for.
        GEPOperator *gep = (srcPointer ? dyn_cast<GEPOperator>(srcPointer) : nullptr);
        //"basePointerType" refers to the type of the pointer operand in the original GEP instruction/opearator, during whose visit we
        //call this makePointsToCopy().
        Type *basePointerType = (gep ? gep->getPointerOperand()->getType() : nullptr);
        Type *basePointToType = (basePointerType ? basePointerType->getPointerElementType() : nullptr);
        InstLoc *loc = new InstLoc(propInstruction,this->currFuncCallSites);
        for (PointerPointsTo *currPointsToObj : *srcPointsTo) {
            if (!currPointsToObj || !currPointsToObj->targetObject) {
                continue;
            }
            PointerPointsTo *pto = currPointsToObj->makeCopyP();
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): basePointerType: " << InstructionUtils::getTypeStr(basePointerType)
            << " cur pto: " << InstructionUtils::getTypeStr(pto->targetObject->targetType) << " | " << pto->dstfieldId
            << ", obj: " << (const void*)(pto->targetObject) <<  " dst fid: " << fieldId << " is_var_fid: " << is_var_fid << "\n";
#endif
            //Try to match the pto w/ the GEP base pointee type.
            int r = this->matchPtoTy(basePointToType,pto,propInstruction);
            AliasObject *hostObj = pto->targetObject;
            long hostfid = pto->dstfieldId;
            auto to_check = std::make_pair(hostfid, hostObj);
            if(std::find(visitedObjects.begin(), visitedObjects.end(), to_check) != visitedObjects.end()) {
                //Already visited the obj|field.
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): this pto was processed before.\n";
#endif
                continue;
            }
            visitedObjects.insert(to_check);
            //Some common assignments.
            pto->fieldId = 0;
            pto->targetPointer = srcPointer;
            pto->propagatingInst = loc;
            if (r > 0) {
                //The pointee can be matched w/ the gep base pointer
                //First perform a boundary check for the new fieldId.
                if (!InstructionUtils::isIndexValid(basePointToType,fieldId)) {
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): base pointer matched but new field id is OOB!\n";
#endif
                    goto fail_next;
                }
                if (r == 1 || r == 3) {
                    //Need to get/create the field embed object..
                    assert(InstructionUtils::same_types(hostObj->getFieldTy(hostfid),basePointToType));
                    AliasObject *newObj = this->createEmbObj(hostObj,hostfid,gep->getPointerOperand(),propInstruction);
                    if (newObj) {
                        pto->targetObject = newObj;
                        pto->dstfieldId = fieldId;
                    }else {
                        //This seems strange...
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "!!! AliasAnalysisVisitor::makePointsToCopy(): cannot get or create embedded object: " 
                        << InstructionUtils::getValueStr(gep) << "\n";
#endif
                        goto fail_next;
                    }
                }else {
                    //We can directly change the field in this case, since the host object already matches the base pointer now.
                    assert(InstructionUtils::same_types(hostObj->targetType,basePointToType));
                    pto->dstfieldId = fieldId;
                }
                newPointsToInfo->insert(pto);
            }else {
                //Fail to match the base pointer type...
                //TODO: what should we do? Discard this pto? Try to invoke bit2field()? Keep the pto anyway?
#ifdef DEBUG_GET_ELEMENT_PTR
                dbgs() << "!!! AliasAnalysisVisitor::makePointsToCopy(): fail to match the base gep pointer!\n";
#endif
                goto fail_next;
            }
            continue;
fail_next:
            delete(pto);
        }
        if (newPointsToInfo->empty()) {
            delete(newPointsToInfo);
            newPointsToInfo = nullptr;
        }
#ifdef DEBUG_GET_ELEMENT_PTR
        if (newPointsToInfo) {
            for (PointerPointsTo *p : *newPointsToInfo) {
                dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): ++ ret pto: " 
                << InstructionUtils::getTypeStr(p->targetObject->targetType) << " | " << p->dstfieldId
                << ", obj: " << (const void*)(p->targetObject) << "\n";
            }
            dbgs() << "AliasAnalysisVisitor::makePointsToCopy(): #ret: " << newPointsToInfo->size() << "\n";
        }
#endif
        return newPointsToInfo;
    }

std::set<PointerPointsTo*>* AliasAnalysisVisitor::mergePointsTo(std::set<Value*> &valuesToMerge, 
                                                                Instruction *targetInstruction, Value *targetPtr) {
    /***
     * Merge pointsToInformation of all the objects pointed by pointers in
     * valuesToMerge
     *
     * targetPtr(if not null) is the pointer that points to all objects in the merge set.
     */
    // Set of pairs of field and corresponding object.
    std::set<std::pair<long, AliasObject*>> targetObjects;
    targetObjects.clear();
    for(Value *currVal : valuesToMerge) {
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
            PointerPointsTo* currPointsToObj = new PointerPointsTo(targetPtr ? targetPtr : targetInstruction, 0, 
                                              currItem.second, currItem.first, new InstLoc(targetInstruction,this->currFuncCallSites), false);
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
#ifdef DEBUG_ALLOCA_INSTR
    dbgs() << "Processed Alloca Instruction, Created new points to information:" << (*newPointsTo) << "\n";
#endif
    this->updatePointsToObjects(&I, targetObj, new InstLoc(&I,this->currFuncCallSites));
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
        for(PointerPointsTo *currPointsToObj : *srcPointsToInfo) {
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
            newPointsToObj->propagatingInst = new InstLoc(&I,this->currFuncCallSites);
            newPointsToObj->targetPointer = &I;
            Type *currTgtObjType = newPointsToObj->targetObject->targetType;
#ifdef DEBUG_CAST_INSTR
            dbgs() << "AliasAnalysisVisitor::visitCastInst(): current target object: " 
            << InstructionUtils::getTypeStr(currTgtObjType) << " | " << currPointsToObj->dstfieldId << "\n";
#endif
            if (dstPointeeTy) {
                this->matchPtoTy(dstPointeeTy,newPointsToObj,&I);
            }else {
#ifdef DEBUG_CAST_INSTR
                dbgs() << "AliasAnalysisVisitor::visitCastInst(): the cast destination is not a pointer\
                , simply propagate the point-to record from src to dst...\n";
#endif
            }
            newPointsToInfo->insert(newPointsToObj);
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

//TODO: we need to handle the potential pointer arithmetic here...
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
                this->createOutsideObj(v,&I,true);
            }
        }
    }
#endif
    std::set<PointerPointsTo*>* finalPointsToInfo = mergePointsTo(allVals, &I);
    if(finalPointsToInfo != nullptr) {
        // Update the points to object of the current instruction.
#ifdef DEBUG_BINARY_INSTR
        dbgs() << "Updating points to information in the binary instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        this->updatePointsToObjects(&I, finalPointsToInfo);
    } else {
#ifdef DEBUG_BINARY_INSTR
        dbgs() << "No value is a pointer in the binary instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
    }

    // Sanity,
    // it is really weired if we are trying to do a binary operation on 2-pointers
    if(hasPointsToObjects(I.getOperand(0)) && hasPointsToObjects(I.getOperand(1))) {
#ifdef DEBUG_BINARY_INSTR
        dbgs() << "WARNING: Trying to perform binary operation on 2-pointers: " << InstructionUtils::getValueStr(&I) << "\n";
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
            this->createOutsideObj(v,&I,true);
        }
    }
    */
#endif

    std::set<PointerPointsTo*>* finalPointsToInfo = mergePointsTo(allVals, &I);
    if(finalPointsToInfo != nullptr) {
        // Update the points to object of the current instruction.
        this->updatePointsToObjects(&I, finalPointsToInfo);
#ifdef DEBUG_PHI_INSTR
        dbgs() << "Merging points to information in the PHI instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
    } else {
#ifdef DEBUG_PHI_INSTR
        dbgs() << "None of the operands are pointers in the PHI instruction: " << InstructionUtils::getValueStr(&I) << "\n";
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
            this->createOutsideObj(v,&I,true);
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
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): Try to create an OutsideObject for srcPointer: " 
            << InstructionUtils::getValueStr(srcPointer) << "\n";
#endif
            this->createOutsideObj(srcPointer,propInst,true);
        }
#endif
        if (!hasPointsToObjects(srcPointer)) {
            //No way to sort this out...
#ifdef DEBUG_GET_ELEMENT_PTR
            errs() << "AliasAnalysisVisitor::processGEPFirstDimension(): No points-to for: " 
            << InstructionUtils::getValueStr(srcPointer) << ", return\n";
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
            np->propagatingInst = new InstLoc(propInst,this->currFuncCallSites);
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
            //struct element from an array, so we just return the original pointee (i.e. collapse the whole array to one element).
            if (basePointeeTy && InstructionUtils::isPrimitiveTy(basePointeeTy)) {
                return nullptr;
            }else {
                return srcPointsTo;
            }
        }
        long index = CI->getSExtValue();
#ifdef DEBUG_GET_ELEMENT_PTR
        dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension():: basePointeeTy: " 
        << InstructionUtils::getTypeStr(basePointeeTy) << " 0st index: " << index << "\n";
#endif
        std::set<PointerPointsTo*> *resPointsTo = new std::set<PointerPointsTo*>();
        DataLayout *dl = this->currState.targetDataLayout;
        if (basePointeeTy && dl && index) {
            bool is_primitive = InstructionUtils::isPrimitiveTy(basePointeeTy);
            //NOTE: we use alloc size here since 1st GEP index is intended to index an array 
            //of the basePointeeTy (i.e. the basePointeeTy will be stored consecutively so we need its alloc size).
            unsigned width = dl->getTypeAllocSizeInBits(basePointeeTy);
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): basePointeeTy size: " 
            << width << ", is_primitive: " << is_primitive << "\n";
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
                PointerPointsTo *newPto = new PointerPointsTo(I, 0, currPto->targetObject, currPto->dstfieldId, 
                                                              new InstLoc(propInst,this->currFuncCallSites), false);
                //Type match in the object parent/embed hierarchy.
                bool ty_match = matchPtoTy(basePointeeTy,newPto,propInst);
                if (newPto->inArray(basePointeeTy)) {
                    //We will not invoke bit2Field() to do the pointer arithmetic in one 
                    //situation: host object is an array of the basePointeeTy (i.e. we are array-insensitive).
#ifdef DEBUG_GET_ELEMENT_PTR
                    dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): ignore the 1st index since we're in an array.\n";
#endif
                    resPointsTo->insert(newPto);
                } else {
                    if (!is_primitive) {
                        //The 1st index is not for an array, instead it's for pointer arithmetic, 
                        //this usually only happens when the GEP base pointee is primitive (e.g. i8)
                        //in which case the GEP has just one index, but now we have a non-primitive 
                        //base pointer for pointer arithmetic (and the GEP can have multiple indices)...
                        //What we do here is we convert this GEP to a one-index GEP w/ primitive base 
                        //pointee, by calculating the overall bit offset of this multi-index GEP. 
                        int rc;
                        index = InstructionUtils::calcGEPTotalOffsetInBits(I,dl,&rc);
                        if (rc) {
                            //This means we fail to calculate the total offset of current GEP... No way to handle it then.
#ifdef DEBUG_GET_ELEMENT_PTR
                            dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): fail to get the\
                            total offset of current non-primitive GEP to handle the non-zero 1st index...\n";
#endif
                            continue;
                        }
#ifdef DEBUG_GET_ELEMENT_PTR
                        dbgs() << "AliasAnalysisVisitor::processGEPFirstDimension(): calculated offset sum in bits: " << index << "\n";
#endif
                        width = 1; //bit unit.
                        //Tell the visitGEP() that it doesn't need to process the remainig indices 
                        //(if any) since we have converted this GEP to single-index for this pto.
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

    //Starting from "dstfieldId" in the target object (struct) as specified in "pto", 
    //if we step bitWidth*index bits, which field will we point to then?
    //The passed-in "pto" will be updated to point to the resulted object and field. 
    //(e.g. we may end up reaching a field in an embed obj in the host obj).
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
            DRCHECKER::createHostObjChain((*tydesc)[i_dstfield],pto,limit,new InstLoc(propInst,this->currFuncCallSites));
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
        int r = DRCHECKER::createEmbObjChain(fd,pto,limit,new InstLoc(propInst,this->currFuncCallSites));
        if (r > limit) {
            //There must be something wrong in the createEmbObjChain()...
#ifdef DEBUG_GET_ELEMENT_PTR
            dbgs() << "!!! AliasAnalysisVisitor::bit2Field(): something wrong w/ the createEmbObjChain()\
            , point-to result will be unreliable, discard..\n";
#endif
            return -1;
        }
        return 0;
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
                errs() << "AliasAnalysisVisitor::visitLoadInst(): No point-to info, after stripping the pointer casts -0, srcPointer: " 
                << InstructionUtils::getValueStr(srcPointer) << "\n";
#endif
            }
        }

        // strip pointer casts. if we cannot find any points to for the srcPointer.
        if(!hasPointsToObjects(srcPointer)) {
            srcPointer = srcPointer->stripPointerCasts();
#ifdef DEBUG_LOAD_INSTR
            errs() << "AliasAnalysisVisitor::visitLoadInst(): No point-to info, after stripping the pointer casts -1, srcPointer: " 
            << InstructionUtils::getValueStr(srcPointer) << "\n";
#endif
        }

#ifdef CREATE_DUMMY_OBJ_IF_NULL
        //hz: try to create dummy objects if there is no point-to information about the pointer variable,
        if(!InstructionUtils::isAsanInst(&I) && !hasPointsToObjects(srcPointer)) {
            this->createOutsideObj(srcPointer,&I,true);
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
            currObjPair.second->fetchPointsToObjects(currObjPair.first, finalObjects, propInst);
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
        GEPOperator *gep = dyn_cast<GEPOperator>(targetPointer);
        if(gep && gep->getNumOperands() > 0 && gep->getPointerOperand() && !dyn_cast<GetElementPtrInst>(targetPointer)) {
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
            if(this->createOutsideObj(targetValue_pre_strip,&I,true)){
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
        std::string fn("file");
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
        OutsideObject *newObj = DRCHECKER::createOutsideObj(file_ty);
        InstLoc *propInst = new InstLoc(&I,this->currFuncCallSites);
        if (newObj) {
            //Since this is a fd, we always treat it as a global taint source.
            newObj->setAsTaintSrc(propInst,true);
            //Update the field point-to according to the "fdFieldMap" and the global pto record if necessary.
            for (auto &e : fdFieldMap) {
                long fid = e.first;
                long arg_no = e.second;
                if (arg_no == -1) {
                    //this means the function return value should point to the newly created file struct.
                    this->updatePointsToObjects(&I, newObj, propInst);
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
#ifdef INFER_XENTRY_SHARED_OBJ
            DRCHECKER::addToSharedObjCache(newObj);
#endif
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
