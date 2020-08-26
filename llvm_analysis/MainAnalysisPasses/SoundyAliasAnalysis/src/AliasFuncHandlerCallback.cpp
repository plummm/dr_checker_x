//
// Created by machiry on 12/4/16.
//

#include "AliasFuncHandlerCallback.h"
#include "AliasObject.h"

using namespace llvm;

namespace DRCHECKER {
    void* AliasFuncHandlerCallback::handleAllocationFunction(CallInst &callInst, Function *targetFunction,
                                                            void *private_data) {
        // Just create a new object
        return createNewHeapObject(callInst, targetFunction, private_data);

    }

    void* AliasFuncHandlerCallback::handleCustomFunction(CallInst &callInst, Function *targetFunction,
                                                        void *private_data) {
        // Create a new heap object
        return createNewHeapObject(callInst, targetFunction, private_data);

    }

    void AliasFuncHandlerCallback::setPrivateData(void *data) {
        this->currState = (GlobalState*)data;
    }

    void* AliasFuncHandlerCallback::createNewHeapObject(CallInst &callInst, Function *targetFunction,
                                                       void *private_data) {

        std::vector<Instruction *> *callSitesContext = (std::vector<Instruction *> *)private_data;
        Value *targetSize = nullptr;
        // if the call is to kmalloc, get the size argument.
        if(this->targetChecker->is_kmalloc_function(targetFunction)) {
            targetSize = callInst.getArgOperand(0);
        }
        Type *objTy = targetFunction->getReturnType();
        if (objTy && objTy->isPointerTy()) {
            objTy = objTy->getPointerElementType();
        }
        AliasObject *targetObj = new HeapLocation(callInst, objTy, callSitesContext, targetSize,
                                                  this->targetChecker->is_kmalloc_function(targetFunction));
        // OK, this is kmalloc function, now check if this is kzmalloc?
        if(this->targetChecker->is_kmalloc_function(targetFunction)) {
            Value *kmalloc_flag = callInst.getArgOperand(1);
            RangeAnalysis::Range flag_range = this->currState->getRange(kmalloc_flag);
            if(flag_range.isBounded()) {
                uint64_t lb =flag_range.getLower().getZExtValue();
                uint64_t ub = flag_range.getUpper().getZExtValue();
                // These are the flag values given when kzalloc is called.
                if((lb & 0x8000) || (ub & 0x8000)) {
                    targetObj->is_initialized = true;
                    targetObj->initializingInstructions.insert(&callInst);
                }
            }
        } else {
            targetObj->is_initialized = true;
            targetObj->initializingInstructions.insert(&callInst);
        }

        //HZ: we also need to treat heap objects as taint source...
        InstLoc *propInst = new InstLoc(&callInst,callSitesContext);
        targetObj->setAsTaintSrc(propInst,true);

        PointerPointsTo *newPointsTo = new PointerPointsTo(&callInst,targetObj,0,propInst,false);
        std::set<PointerPointsTo*> *newPointsToInfo = new std::set<PointerPointsTo*>();
        newPointsToInfo->insert(newPointsToInfo->end(), newPointsTo);
        return newPointsToInfo;

    }
}
