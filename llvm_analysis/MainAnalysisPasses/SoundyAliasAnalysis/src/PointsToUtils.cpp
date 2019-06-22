//
// Created by machiry on 12/6/16.
//

#include "PointsToUtils.h"
#include "../../Utils/include/InstructionUtils.h"

using namespace llvm;

namespace DRCHECKER {
//#define DEBUG_FUNCTION_PTR_ALIASING
#define DEBUG_SMART_FUNCTION_PTR_RESOLVE

    std::set<PointerPointsTo*>* PointsToUtils::getPointsToObjects(GlobalState &currState,
                                                                  std::vector<Instruction *> *currFuncCallSites,
                                                                  Value *srcPointer) {
        // Get points to objects set of the srcPointer at the entry of the instruction
        // currInstruction.
        // Note that this is at the entry of the instruction. i.e INFLOW.
        std::map<Value *, std::set<PointerPointsTo*>*>* targetPointsToMap = currState.getPointsToInfo(currFuncCallSites);
        // Here srcPointer should be present in points to map.
        if(targetPointsToMap->find(srcPointer) != targetPointsToMap->end()) {
            return (*targetPointsToMap)[srcPointer];
        }
        return nullptr;

    }

    bool PointsToUtils::hasPointsToObjects(GlobalState &currState,
                                           std::vector<Instruction *> *currFuncCallSites,
                                           Value *srcPointer) {
        /***
         * Check if the srcPointer has any pointto objects at currInstruction
         */
        std::map<Value *, std::set<PointerPointsTo*>*>* targetPointsToMap = currState.getPointsToInfo(currFuncCallSites);
        return targetPointsToMap != nullptr &&
               targetPointsToMap->find(srcPointer) != targetPointsToMap->end();
    }

    bool PointsToUtils::getTargetFunctions(GlobalState &currState, std::vector<Instruction *> *currFuncCallSites,
                                           Value *srcPointer, std::vector<Function *> &dstFunctions) {
        // first get the type of the function we are looking for.
        Type *targetFunctionType = srcPointer->getType();
        bool retVal = false;

        // get points to information, handling casts.
        std::set<PointerPointsTo*>* basePointsTo = PointsToUtils::getPointsToObjects(currState, currFuncCallSites,
                                                                                     srcPointer);
        if(basePointsTo == nullptr) {
            basePointsTo = PointsToUtils::getPointsToObjects(currState, currFuncCallSites,
                                                             srcPointer->stripPointerCasts());
        }

        // OK, we have some points to information for the srcPointer.
        if(basePointsTo != nullptr) {
            for(PointerPointsTo *currPointsTo: *(basePointsTo)) {
                // OK, this is a global object.
                if(currPointsTo->targetObject->isGlobalObject()) {
                    // Check if it is function.
                    GlobalObject *currGlobObj = (GlobalObject*)(currPointsTo->targetObject);
                    Function *targetFunction = dyn_cast<Function>(currGlobObj->targetVar);
                    if(targetFunction != nullptr) {
                        if (InstructionUtils::same_types(targetFunction->getType(), targetFunctionType)) {
                            retVal = true;
                            dstFunctions.push_back(targetFunction);
#ifdef DEBUG_FUNCTION_PTR_ALIASING
                            dbgs() << "Found Target Function:" << targetFunction->getName() << " for Pointer:";
                            srcPointer->print(dbgs());
                            dbgs() << "\n";
#endif
                        } else {
#ifdef DEBUG_FUNCTION_PTR_ALIASING
                            dbgs()
                                    << "Function pointer points to a function whose type does not match the pointer type.\n";
                            dbgs() << "Pointer Type:";
                            targetFunctionType->print(dbgs());
                            dbgs() << "\n";
                            dbgs() << "Destination Function Type:";
                            targetFunction->getType()->print(dbgs());
                            dbgs() << "\n";
#endif

                        }
                    }
                }
            }
        }
        return retVal;
    }

    bool PointsToUtils::getAllAliasObjects(GlobalState &currState, std::vector<Instruction *> *currFuncCallSites,
                            Value *srcPointer,
                            std::set<AliasObject*> &dstObjects) {
        std::set<PointerPointsTo*>* pointsToSet = PointsToUtils::getPointsToObjects(currState,
                                                                                    currFuncCallSites, srcPointer);
        bool addedAtleastOne = false;
        if(pointsToSet != nullptr) {
            for(auto currp:*pointsToSet) {
                // if the current object is not present?
                // then add the object into the dstObjects.
                if(dstObjects.find(currp->targetObject) == dstObjects.end()) {
                    dstObjects.insert(currp->targetObject);
                    addedAtleastOne = true;
                }
            }
        }
        return addedAtleastOne;
    }

    bool PointsToUtils::getPossibleFunctionTargets(CallInst &callInst, std::vector<Function *> &targetFunctions) {
        //Set up a cache to accelerate the lookup.
        static std::map<Module*,std::map<FunctionType*,std::vector<Function*>>> target_cache;
        FunctionType *targetFunctionType = callInst.getFunctionType();
#ifdef DEBUG_SMART_FUNCTION_PTR_RESOLVE
        dbgs() << "PointsToUtils::getPossibleFunctionTargets: try to resolve a indirect function call w/ type-based method: ";
        dbgs() << InstructionUtils::getValueStr(&callInst) << "\n";
        dbgs() << "Callee type: " << InstructionUtils::getTypeStr(targetFunctionType) << "\n";
#endif
        Module *currModule = callInst.getParent()->getParent()->getParent();
        if (target_cache.find(currModule) != target_cache.end() && target_cache[currModule].find(targetFunctionType) != target_cache[currModule].end()) {
            //targetFunctions.insert(target_cache[currModule][targetFunctionType].begin(),target_cache[currModule][targetFunctionType].end());
            targetFunctions = target_cache[currModule][targetFunctionType];
            return true;
        }
        for(auto a = currModule->begin(), b = currModule->end(); a != b; a++) {
            Function *currFunction = &(*a);
            // does the current function has same type of the call instruction?
            if(!currFunction->isDeclaration() && InstructionUtils::same_types(currFunction->getFunctionType(), targetFunctionType)) {
#ifdef DEBUG_SMART_FUNCTION_PTR_RESOLVE
                dbgs() << "PointsToUtils::getPossibleFunctionTargets: Got a same-typed candidate callee: ";
                dbgs() << currFunction->getName().str() << "\n";
#endif
                //Do some further filtering based on some heuristics
                //(1) the func appears in a non-call instruction, indicating a function pointer assignment
                //(2) the func appears in a constant structure, possibly as a function pointer field.
                //Now we only use (2) since in driver most cases are like "dev->ops->xxx()"
                for (Value::user_iterator i = currFunction->user_begin(), e = currFunction->user_end(); i != e; ++i) {
                    Instruction *currI = dyn_cast<Instruction>(*i);
                    CallInst *currC = dyn_cast<CallInst>(*i);
                    ConstantAggregate *currConstA = dyn_cast<ConstantAggregate>(*i);
                    GlobalValue *currGV = dyn_cast<GlobalValue>(*i);
#ifdef DEBUG_SMART_FUNCTION_PTR_RESOLVE
                    //dbgs() << "USE: " << InstructionUtils::getValueStr(*i) << "### " << (currI!=nullptr) << "|" << (currC!=nullptr) << "|" << (currConstA!=nullptr) << "|" << (currGV!=nullptr) << "\n";
#endif
                    //if(currConstA != nullptr) {
                    if(currI != nullptr && currC == nullptr) {
#ifdef DEBUG_SMART_FUNCTION_PTR_RESOLVE
                        dbgs() << "PointsToUtils::getPossibleFunctionTargets: add to final list since the candidate has been used in a non-call inst.\n";
#endif
                        // oh the function is used in a non-call instruction.
                        // potential target, insert into potential targets
                        targetFunctions.push_back(currFunction);
                        break;
                    }
                }
            }
        }

        PointsToUtils::filterPossibleFunctionsByLoc(&callInst, targetFunctions);

        if (targetFunctions.size() > 0) {
            //target_cache[currModule][targetFunctionType].insert(targetFunctions.begin(),targetFunctions.end());
            target_cache[currModule][targetFunctionType] = targetFunctions;
            return true;
        }
        return false;
    }

    void PointsToUtils::filterPossibleFunctionsByLoc(Instruction *inst, std::vector<Function *> &targetFunctions) {
        if (!inst) {
            return;
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
    }

    bool PointsToUtils::getTargetObjects(std::set<PointerPointsTo*> *dstPointsTo, std::set<std::pair<long, AliasObject*>> &targetObjects) {
        if (!dstPointsTo || dstPointsTo->empty()) {
            return false;
        }
        for (PointerPointsTo *currPointsToObj:*dstPointsTo) {
            long target_field = currPointsToObj->dstfieldId;
            AliasObject *dstObj = currPointsToObj->targetObject;
            auto to_check = std::make_pair(target_field, dstObj);
            if (std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                targetObjects.insert(targetObjects.end(), to_check);
            }
        }
        return true;
    }

};
