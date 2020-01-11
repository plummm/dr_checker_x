//
// Created by machiry on 10/25/16.
//

#ifndef PROJECT_MODULESTATE_H
#define PROJECT_MODULESTATE_H
#include "AliasObject.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "TaintInfo.h"
#include "bug_detectors/warnings/VulnerabilityWarning.h"
#include "RangeAnalysis.h"
#include <set>
#include <chrono>
#include <ctime>
#include <fstream>
#include "../../Utils/include/InstructionUtils.h"
//for cereal serialization
/*
#include "cereal/archives/xml.hpp"
//#include "../../cereal/archives/portable_binary.hpp"
#include "cereal/types/map.hpp"
#include "cereal/types/vector.hpp"
#include "cereal/types/set.hpp"
#include "cereal/types/tuple.hpp"
#include "cereal/types/string.hpp"
*/
#include "ResType.h"
#include "../../Utils/include/json.hpp"
using json = nlohmann::json;

#define DEBUG_TAINT_DUMP_PROGRESS
#define DEBUG_TAINT_SERIALIZE_PROGRESS
//#define DEBUG_HIERARCHY

using namespace llvm;

namespace DRCHECKER {
//#define DEBUG_GLOBALS
    /***
     * Class that abstracts the context.
     * Definition 3.5 of the paper.
     */
    class AnalysisContext {
    public:
        std::vector<Instruction *> *callSites;
        void printContext(llvm::raw_ostream& O) {
            O << "\"context\":[";
            bool putComma = false;
            //std::string str;
            for(Instruction *currCallSite:*(this->callSites)) {
                if(putComma) {
                    O << ",";
                }

                O << "{\"instr\":\"";
                //currCallSite->print(O);
                //DILocation *instrLoc = currCallSite->getDebugLoc().get();
                DILocation *instrLoc = InstructionUtils::getCorrectInstrLocation(currCallSite);
                O << InstructionUtils::escapeValueString(currCallSite) << "\",";
                O << "\"lineno\":";
                if (instrLoc != nullptr) {
                    //O << ", src line:" << instrLoc->getLine() << " file:" << instrLoc->getFilename();
                    O << instrLoc->getLine() << ",\"file\":\"";
                    O << InstructionUtils::escapeJsonString(instrLoc->getFilename()) << "\"";
                } else {
                    O << "-1";
                }
                O << "}\n";
                putComma = true;
            }
            O << "\n]";
        }

    };

    /***
     *  Object which represents GlobalState.
     *  Everything we need in one place.
     *  Refer Fig1 in the paper.
     *  It contains pointsTo, globalVariables and TaintInformation.
     */
    class GlobalState {
    public:

        // map containing analysis context to corresponding vulnerability warnings.
        std::map<AnalysisContext*, std::set<VulnerabilityWarning*>*> allVulnWarnings;

        // map containing vulnerability warnings w.r.t instruction.
        std::map<Instruction*, std::set<VulnerabilityWarning*>*> warningsByInstr;
        // set containing all analysis contexts that were analyzed using this global state
        std::set<AnalysisContext*> availableAnalysisContexts;

        // Range analysis results.
        RangeAnalysis::RangeAnalysis *range_analysis;

        //is the current function being analyzed read/write?
        bool is_read_write_function = false;

        // Map, which contains at each instruction.
        // set of objects to which the pointer points to.
        // Information needed for AliasAnalysis
        std::map<AnalysisContext*, std::map<Value *, std::set<PointerPointsTo*>*>*> pointToInformation;
        static std::map<Value *, std::set<PointerPointsTo*>*> globalVariables;

        static std::map<Function *, std::set<BasicBlock*>*> loopExitBlocks;


        // Data layout for the current module
        DataLayout *targetDataLayout;

        // Information needed for TaintAnalysis
        std::map<AnalysisContext*, std::map<Value *, std::set<TaintFlag*>*>*> taintInformation;

        //hz: the mapping between BBs in a switch-case structure to the leading switch variable values. 
        std::map<BasicBlock*,std::set<uint64_t>> switchMap;

        //hz: records the update pattern of the store insts, e.g., a = 0 or a++
        std::map<StoreInst*,std::map<std::vector<Instruction*>*,TRAIT>> modTraitMap;

        //hz: records the branch condition pattern, e.g., a == 0 or a > 1
        std::map<BranchInst*,std::map<std::vector<Instruction*>*,TRAIT>> brTraitMap;

        //hz: func name -> call inst -> set of ctx ptr
        std::map<std::string,std::map<CallInst*,std::set<std::vector<Instruction*>*>>> calleeMap;

        // a map of basic block to number of times it is analyzed.
        std::map<const BasicBlock*, unsigned long> numTimeAnalyzed;


        GlobalState(RangeAnalysis::RangeAnalysis *ra, DataLayout *currDataLayout) {
            this->range_analysis = ra;
            this->targetDataLayout = currDataLayout;
        }

        ~GlobalState() {
            cleanup();

        }

        void cleanup() {
            // clean up
            std::set<AliasObject*> deletedObjects;
            // all global variables.
            for(auto glob_iter = globalVariables.begin(); glob_iter != globalVariables.end(); glob_iter++) {
                auto targetPointsTo = glob_iter->second;
                for(auto currPointsTo: *targetPointsTo) {
                    auto targetAliasObj = currPointsTo->targetObject;
                    if(deletedObjects.find(targetAliasObj) == deletedObjects.end()) {
                        deletedObjects.insert(targetAliasObj);
                        delete(targetAliasObj);
                    }
                    delete(currPointsTo);
                }
                delete(targetPointsTo);
            }
            globalVariables.clear();

            // all pointsToInformation
            for(auto ptInfo = pointToInformation.begin(); ptInfo != pointToInformation.end(); ptInfo++) {
                for(auto pointsTo_iter = ptInfo->second->begin(); pointsTo_iter != ptInfo->second->begin();
                    pointsTo_iter++) {
                    auto targetPointsTo = pointsTo_iter->second;
                    for(auto currPointsTo: *targetPointsTo) {
                        auto targetAliasObj = currPointsTo->targetObject;
                        if(deletedObjects.find(targetAliasObj) == deletedObjects.end()) {
                            deletedObjects.insert(targetAliasObj);
                            delete(targetAliasObj);
                        }
                        delete(currPointsTo);
                    }
                    delete(targetPointsTo);
                }
            }
            pointToInformation.clear();
        }

        /***
         * Get the DataLayout for the current module being analyzed.
         * @return pointer to the DataLayout*
         */
        DataLayout* getDataLayout() {
            return this->targetDataLayout;
        }

        /***
         * Get the type size for the provided type.
         * @param currType Type for which size needs to fetched.
         * @return uint64_t representing size of the type.
         */
        uint64_t getTypeSize(Type *currType) {
            if(currType->isSized()) {
                return this->getDataLayout()->getTypeAllocSize(currType);
            }
            return 0;
        }


        /***
         * Get the AliasObject referenced by the currVal.
         *
         * @param currVal Value whose reference needs to be fetched.
         * @param globalObjectCache Map containing values and corresponding
         *                          AliasObject.
         * @return Corresponding AliasObject.
         */
        static AliasObject* getReferencedGlobal(std::vector<llvm::GlobalVariable *> &visitedCache, Value *currVal,
                                                std::map<Value*, AliasObject*> &globalObjectCache) {

            llvm::GlobalVariable *actualGlobal = dyn_cast<llvm::GlobalVariable>(currVal);
            if (actualGlobal == nullptr) {
                // OK, check with stripped.
                Value *strippedVal = currVal->stripPointerCasts();
                actualGlobal = dyn_cast<llvm::GlobalVariable>(strippedVal);
            }

            if (actualGlobal == nullptr) {
                ConstantExpr *targetExpr = dyn_cast<ConstantExpr>(currVal);
                if (targetExpr != nullptr) {
                    AliasObject *refObj = nullptr;
                    // Even stripping din't help. Check if this is an instruction and get the first
                    // global variable in operand list
                    for (unsigned int i = 0; i < targetExpr->getNumOperands(); i++) {
                        Value *currOperand = targetExpr->getOperand(i);
                        llvm::GlobalVariable *globalCheck = dyn_cast<llvm::GlobalVariable>(currOperand);
                        if (globalCheck == nullptr) {
                            // check with strip
                            globalCheck = dyn_cast<llvm::GlobalVariable>(currOperand->stripPointerCasts());
                        }
                        if (globalCheck != nullptr) {
                            actualGlobal = globalCheck;
                            break;
                        }
                        refObj = getReferencedGlobal(visitedCache, currOperand, globalObjectCache);
                        if(refObj != nullptr) {
                            return refObj;
                        }
                    }

                }
            }

            if (actualGlobal == nullptr) {
                Function *targetFunction = dyn_cast<Function>(currVal);
                if(targetFunction != nullptr) {
                    if (globalObjectCache.find((Value *) targetFunction) != globalObjectCache.end()) {
                        return globalObjectCache[(Value *) targetFunction];
                    }
                }
            }
            if(actualGlobal != nullptr) {
                return addGlobalVariable(visitedCache, actualGlobal, globalObjectCache);
            }
            return nullptr;
        }

        /***
         *  Check if the Constant is a constant variable. ie. it uses
         *  some global variables.
         * @param targetConstant Constant to check
         * @return true/false depending on whether the constant
         *         references global variable.
         */
        static bool isConstantVariable(Constant *targetConstant) {
            Function* functionCheck = dyn_cast<Function>(targetConstant);
            if(functionCheck) {
                return true;
            }
            llvm::GlobalVariable *globalCheck = dyn_cast<llvm::GlobalVariable>(targetConstant);
            if(globalCheck) {
                return true;
            }
            ConstantExpr *targetExpr = dyn_cast<ConstantExpr>(targetConstant);
            if(targetExpr) {
                return true;
            }
            return false;
        }


        /***
         *  Get the global object from variable initializers.
         * @param constantType Type of the constant.
         * @param targetConstant Constant for which AliasObject needs to be created.
         * @param globalObjectCache Cache containing value to AliasObject.
         * @return Alias Object corresponding to the initializer.
         */
        static AliasObject* getGlobalObjectFromInitializer(std::vector<llvm::GlobalVariable *> &visitedCache,
                                                           Type* constantType, Constant* targetConstant,
                                                     std::map<Value*, AliasObject*> &globalObjectCache) {
            AliasObject *glob = nullptr;
            if(constantType->isStructTy()) {
                glob = new GlobalObject(targetConstant, constantType);
                ConstantStruct *actualStType = dyn_cast<ConstantStruct>(targetConstant);
                if(actualStType != nullptr) {
                    for (unsigned int i = 0; i < actualStType->getNumOperands(); i++) {
                        Value *currFieldVal = actualStType->getOperand(i);
                        AliasObject *currFieldObj = nullptr;
                        Constant *constCheck = dyn_cast<Constant>(currFieldVal);
                        if(isConstantVariable(constCheck)) {
                            // OK, the field is initialized but it is not a constant?
                            // check if this is a global variable?
                            currFieldObj = getReferencedGlobal(visitedCache, currFieldVal, globalObjectCache);
                        }
                        else {
                            // the field is initialized with constant?
                            currFieldObj = getGlobalObjectFromInitializer(visitedCache,
                                                                          currFieldVal->getType(), constCheck,
                                                                          globalObjectCache);
                        }
                        if (currFieldObj != nullptr) {
                            glob->addObjectToFieldPointsTo(i, currFieldObj, nullptr);
                        }
                    }
                }

            } else if(constantType->isAggregateType()) {
                glob = new GlobalObject(targetConstant, constantType);
            }
            return glob;

        }


        /***
         * Add global variable into the global state and return corresponding AliasObject.
         *
         * Handles global variables in a rather complex way.
         * A smart person should implement this in a better way.
         *
         *
         * @param globalVariable Global variable that needs to be added.
         * @param globalObjectCache Cache of Values to corresponding AliasObject.
         * @return AliasObject corresponding to the global variable.
         */
        static AliasObject* addGlobalVariable(std::vector<llvm::GlobalVariable *> &visitedCache,
                                              llvm::GlobalVariable *globalVariable,
                                      std::map<Value*, AliasObject*> &globalObjectCache) {

            if(std::find(visitedCache.begin(), visitedCache.end(), globalVariable) != visitedCache.end()) {
#ifdef DEBUG_GLOBALS
                dbgs() << "Cycle Detected for:";
                globalVariable->print(dbgs());
                dbgs() << "\n";
#endif
                return nullptr;
            }

            Value *objectCacheKey = dyn_cast<Value>(globalVariable);
            AliasObject *toRet = nullptr;
            assert(objectCacheKey != nullptr);
            // if its already processed? Return previously created object.
            if(globalObjectCache.find(objectCacheKey) != globalObjectCache.end()) {
                return globalObjectCache[objectCacheKey];
            } else {

                visitedCache.push_back(globalVariable);

                // OK, the global variable has no initializer.
                // Just create a default object.
                std::set<PointerPointsTo *> *newPointsTo = new std::set<PointerPointsTo *>();


                // This is new global variable.
                Type *baseType = globalVariable->getType();
                // global variables are always pointers
                assert(baseType->isPointerTy());
                // next check if it has any initializers.
                if (globalVariable->hasInitializer()) {
                    Constant *baseInitializer = globalVariable->getInitializer();
                    toRet = getGlobalObjectFromInitializer(visitedCache, baseInitializer->getType(),
                                                           baseInitializer, globalObjectCache);

                }

                if(toRet == nullptr) {
                    // OK, the global variable has no initializer.
                    // Just create a default object.
                    toRet = new GlobalObject(globalVariable, baseType->getContainedType(0));
                }

                PointerPointsTo *pointsToObj = new PointerPointsTo();
                pointsToObj->targetObject = toRet;
                pointsToObj->fieldId = pointsToObj->dstfieldId = 0;
                pointsToObj->propogatingInstruction = globalVariable;
                pointsToObj->targetPointer = globalVariable;
                newPointsTo->insert(newPointsTo->end(), pointsToObj);
                assert(GlobalState::globalVariables.find(globalVariable) == GlobalState::globalVariables.end());
                GlobalState::globalVariables[globalVariable] = newPointsTo;
                //dbgs() << "Adding:" << *globalVariable << " into cache\n";
            }
            // make sure that object cache doesn't already contain the object.
            assert(globalObjectCache.find(objectCacheKey) == globalObjectCache.end());
            // insert into object cache.
            globalObjectCache[objectCacheKey] = toRet;
            // Make sure that we have created a pointsTo information for globals.
            assert(GlobalState::globalVariables.find(globalVariable) != GlobalState::globalVariables.end());
            assert(GlobalState::globalVariables[globalVariable] != nullptr);
            visitedCache.pop_back();
            return toRet;

        }

        /***
         * Add global function into GlobalState.
         * @param currFunction Function that needs to be added.
         * @param globalObjectCache Map of values and corresponding AliasObject.
         */
        static void addGlobalFunction(Function *currFunction, std::map<Value*, AliasObject*> &globalObjectCache) {
            // add to the global cache, only if there is a definition.
            if(!currFunction->isDeclaration()) {
                std::set<PointerPointsTo *> *newPointsTo = new std::set<PointerPointsTo *>();
                GlobalObject *glob = new GlobalObject(currFunction);
                PointerPointsTo *pointsToObj = new PointerPointsTo();
                pointsToObj->targetObject = glob;
                pointsToObj->fieldId = pointsToObj->dstfieldId = 0;
                pointsToObj->propogatingInstruction = currFunction;
                pointsToObj->targetPointer = currFunction;
                newPointsTo->insert(newPointsTo->end(), pointsToObj);

                GlobalState::globalVariables[currFunction] = newPointsTo;
                globalObjectCache[currFunction] = glob;
            }
        }

        /***
         * Add loop exit blocks for the provided function.
         * @param targetFunction Pointer to the function for which the loop exit block needs to be added.
         * @param allExitBBs List of the basicblocks to be added
         */
        static void addLoopExitBlocks(Function *targetFunction, SmallVector<BasicBlock *, 1000> &allExitBBs) {
            if(loopExitBlocks.find(targetFunction) == loopExitBlocks.end()) {
                loopExitBlocks[targetFunction] = new std::set<BasicBlock*>();
            }
            std::set<BasicBlock*> *toAddList;
            toAddList = loopExitBlocks[targetFunction];
            toAddList->insert(allExitBBs.begin(), allExitBBs.end());
        }

        /***
         * Get all loop exit basic blocks for the provided function.
         * @param targetFunction Target function for which the exit blocks needs to be fetched.
         * @return pointer to set of all loop exit basic blocks for the provided function.
         */
        static std::set<BasicBlock*> * getLoopExitBlocks(Function *targetFunction) {
            if(loopExitBlocks.find(targetFunction) != loopExitBlocks.end()) {
                return loopExitBlocks[targetFunction];
            }
            return nullptr;
        }


        // Get the context for the provided instruction at given call sites.
        AnalysisContext* getContext(std::vector<Instruction *> *callSites) {
            for(auto curr_a:availableAnalysisContexts) {
                if(*(curr_a->callSites) == *callSites) {
                    return curr_a;
                }
            }
            return nullptr;
        }


        /***
         *  Get or create context at the provided list of callsites,
         *  with corresponding pointsto and taint information.
         *
         * @param callSites list of call sites for the target context.
         * @param targetInfo Points-To info as std::set<PointerPointsTo*>*>*
         * @param targetTaintInfo Taint into as std::map<Value *, std::set<TaintFlag*>*> *
         * @return Target context updated with the provided information.
         *
         */
        AnalysisContext* getOrCreateContext(std::vector<Instruction *> *callSites, std::map<Value *,
                std::set<PointerPointsTo*>*> *targetInfo = nullptr, std::map<Value *, std::set<TaintFlag*>*> *targetTaintInfo = nullptr) {

            AnalysisContext* currContext = getContext(callSites);
            if(currContext == nullptr) {
                // Create a new context for the provided instruction with provided points to info.
                AnalysisContext *newContext = new AnalysisContext();
                newContext->callSites = callSites;
                // insert the new context into available contexts.
                availableAnalysisContexts.insert(availableAnalysisContexts.end(), newContext);

                // create new points to information.
                std::map<Value *, std::set<PointerPointsTo *> *> *newInfo = new std::map<Value *, std::set<PointerPointsTo *> *>();
                if (targetInfo != nullptr) {
                    newInfo->insert(targetInfo->begin(), targetInfo->end());
                } else {
                    // Add all global variables in to the context.
                    newInfo->insert(GlobalState::globalVariables.begin(), GlobalState::globalVariables.end());
                }
                pointToInformation[newContext] = newInfo;

                // create taint info for the newly created context.
                std::map<Value *, std::set<TaintFlag*>*> *newTaintInfo = new std::map<Value *, std::set<TaintFlag*>*>();
                if(targetTaintInfo != nullptr) {
                    newTaintInfo->insert(targetTaintInfo->begin(), targetTaintInfo->end());
                }
                taintInformation[newContext] = newTaintInfo;

                return newContext;
            }
            return currContext;
        }

        void insertPointsTo(std::vector<Instruction *> *callSites, std::map<Value *, std::set<PointerPointsTo*>*> *targetInfo) {
            AnalysisContext* currContext = getContext(callSites);
            pointToInformation[currContext] = targetInfo;
        }

        void copyPointsToInfo(AnalysisContext *targetContext) {
            // Make a shallow copy of points to info for the current context.
            std::map<Value *, std::set<PointerPointsTo*>*> *currInfo = pointToInformation[targetContext];

            // we need to make a shallow copy of currInfo
            std::map<Value *, std::set<PointerPointsTo*>*> *newInfo = new std::map<Value *, std::set<PointerPointsTo*>*>();
            newInfo->insert(currInfo->begin(), currInfo->end());

            pointToInformation[targetContext] = newInfo;
        }

        /***
         * Get all points to information at the provided context i.e., list of call sites.
         * @param callSites target context: List of call-sites
         * @return PointsTo information as std::map<Value *, std::set<PointerPointsTo*>*>*
         */
        std::map<Value *, std::set<PointerPointsTo*>*>* getPointsToInfo(std::vector<Instruction *> *callSites) {
            AnalysisContext* currContext = getContext(callSites);
            assert(currContext != nullptr && pointToInformation.count(currContext));
            //if(currContext != nullptr && pointToInformation.count(currContext)) {
                return pointToInformation[currContext];
            //}
            //return nullptr;
        }

        // Taint Handling functions

        /***
         * get all taint information at the provided context i.e., list of call sites
         * @param callSites target context: List of call-sites
         * @return Taint information as: std::map<Value *, std::set<TaintFlag*>*>*
         */
        std::map<Value *, std::set<TaintFlag*>*>* getTaintInfo(std::vector<Instruction *> *callSites) {
            AnalysisContext* currContext = getContext(callSites);
            if(currContext != nullptr && taintInformation.count(currContext)) {
                return taintInformation[currContext];
            }
            return nullptr;
        };

        bool in_hierarchy_history(AliasObject *obj, long field, std::vector<std::pair<long, AliasObject*>>& history, bool to_add) {
            auto to_check = std::make_pair(field, obj);
            if (std::find(history.begin(),history.end(),to_check) != history.end()) {
                return true;
            }
            if (to_add) {
                history.push_back(to_check);
            }
            return false;
        }

        std::set<std::string> *getHierarchyStr(AliasObject *obj, long field, int layer, std::vector<std::pair<long, AliasObject*>>& history) {
#ifdef DEBUG_HIERARCHY
            dbgs() << layer << " getHierarchyStr(): " << (obj ? InstructionUtils::getTypeStr(obj->targetType) : "") << " | " << field << " ID: " << (const void*)obj << "\n";
#endif
            if (!obj) {
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " getHierarchyStr(): null obj.\n";
#endif
                return nullptr;
            }
            if (obj->isFunctionLocal()) {
                //We're not interested in function local variables as they are not persistent.
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " getHierarchyStr(): function local objs.\n";
#endif
                return nullptr;
            }
            std::set<std::string> *strs = new std::set<std::string>();
            std::string currStr = InstructionUtils::getTypeStr(obj->targetType) + ":" + std::to_string(field);
            if (this->in_hierarchy_history(obj,field,history,true)) {
                //Exists in the history obj chain, should be a loop..
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " getHierarchyStr(): Exists in the obj chain..\n";
#endif
                strs->insert("<->" + currStr);
                return strs;
            }
            if (obj->parent && obj->parent->embObjs.find(obj->parent_field) != obj->parent->embObjs.end() && obj->parent->embObjs[obj->parent_field] == obj) {
                //Current obj is embedded in another obj.
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " getHierarchyStr(): find a host obj that embeds this one..";
#endif
                std::set<std::string> *rs = getHierarchyStr(obj->parent,obj->parent_field,layer+1,history);
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " getHierarchyStr(): embedded in another obj! #rs: ";
                if (rs) {
                    dbgs() << rs->size();
                }
                dbgs() << "\n";
#endif
                if (rs) {
                    for (auto& x : *rs) {
                        strs->insert(x + "." + currStr);
                    }
                    delete(rs);
                }
            }
            if (!obj->pointsFrom.empty()) {
                //Current obj may be pointed to by a field in another obj.
                std::set<AliasObject*> visitedObjs;
                visitedObjs.clear();
                for (AliasObject *x : obj->pointsFrom) {
                    if (visitedObjs.find(x) != visitedObjs.end()) {
                        //has visited before.
                        continue;
                    }
                    visitedObjs.insert(x);
#ifdef DEBUG_HIERARCHY
                    dbgs() << layer << " getHierarchyStr(): find a host object that can point to this one...\n";
#endif
                    for (ObjectPointsTo *y : x->pointsTo) {
                        if (y->targetObject != obj || (y->dstfieldId > 0 && y->dstfieldId != field)) {
                            continue;
                        }
                        std::set<std::string> *rs = getHierarchyStr(x,y->fieldId,layer+1,history);
#ifdef DEBUG_HIERARCHY
                        dbgs() << layer << " getHierarchyStr(): host point-to, #rs: ";
                        if (rs) {
                            dbgs() << rs->size();
                        }
                        dbgs() << "\n";
#endif
                        if (rs) {
                            for (auto& z : *rs) {
                                strs->insert(z + "->" + currStr);
                            }
                            delete(rs);
                        }
                    }
                }
            }
            if (strs->empty()) {
                strs->insert(currStr);
            }
#ifdef DEBUG_HIERARCHY
            dbgs() << layer << " getHierarchyStr(): #strs: " << strs->size() << "\n";
#endif
            history.pop_back();
            return strs; 
        }

        std::set<std::vector<TypeField*>*> *getHierarchyTy(AliasObject *obj, long field, int layer, std::vector<std::pair<long, AliasObject*>>& history) {
#ifdef DEBUG_HIERARCHY
            dbgs() << layer << " getHierarchyTy(): " << (obj ? InstructionUtils::getTypeStr(obj->targetType) : "") << " | " << field << " ID: " << (const void*)obj << "\n";
#endif
            if (!obj) {
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " getHierarchyTy(): null obj.\n";
#endif
                return nullptr;
            }
            if (obj->isFunctionLocal()) {
                //We're not interested in function local variables as they are not persistent.
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " getHierarchyTy(): function local objs.\n";
#endif
                return nullptr;
            }
            std::set<std::vector<TypeField*>*> *tys = new std::set<std::vector<TypeField*>*>();
            TypeField *currTf = new TypeField(obj->targetType,field,(void*)obj);
            if (this->in_hierarchy_history(obj,field,history,true)) {
                //Exists in the history obj chain, should be a loop..
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " getHierarchyTy(): Exists in the obj chain..\n";
#endif
                std::vector<TypeField*> *currTy = new std::vector<TypeField*>();
                currTy->push_back(currTf);
                tys->insert(currTy);
                return tys;
            }
            if (obj->parent && obj->parent->embObjs.find(obj->parent_field) != obj->parent->embObjs.end() && obj->parent->embObjs[obj->parent_field] == obj) {
                //Current obj is embedded in another obj.
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " getHierarchyTy(): find a host obj that embeds this one..";
#endif
                std::set<std::vector<TypeField*>*> *rty = getHierarchyTy(obj->parent,obj->parent_field,layer+1,history);
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " getHierarchyTy(): embedded in another obj! #rty: " << (rty ? rty->size() : 0) << "\n";
#endif
                if (rty) {
                    for (auto& x : *rty) {
                        x->push_back(currTf);
                        //. (embed field)
                        tys->insert(x);
                    }
                    delete(rty);
                }
            }
            if (!obj->pointsFrom.empty()) {
                //Current obj may be pointed to by a field in another obj.
                std::set<AliasObject*> visitedObjs;
                visitedObjs.clear();
                for (AliasObject *x : obj->pointsFrom) {
                    if (visitedObjs.find(x) != visitedObjs.end()) {
                        //has visited before.
                        continue;
                    }
                    visitedObjs.insert(x);
#ifdef DEBUG_HIERARCHY
                    dbgs() << layer << " getHierarchyTy(): find a host object that can point to this one...\n";
#endif
                    for (ObjectPointsTo *y : x->pointsTo) {
                        if (y->targetObject != obj || (y->dstfieldId > 0 && y->dstfieldId != field)) {
                            continue;
                        }
                        std::set<std::vector<TypeField*>*> *rty = getHierarchyTy(x,y->fieldId,layer+1,history);
#ifdef DEBUG_HIERARCHY
                        dbgs() << layer << " getHierarchyTy(): host point-to, #rty: " << (rty ? rty->size() : 0) << "\n";
#endif
                        if (rty) {
                            for (auto& z : *rty) {
                                z->push_back(currTf);
                                //-> (point-to field)
                                tys->insert(z);
                            }
                            delete(rty);
                        }
                    }
                }
            }
            if (tys->empty()) {
                std::vector<TypeField*> *currTy = new std::vector<TypeField*>();
                currTy->push_back(currTf);
                tys->insert(currTy);
            }
#ifdef DEBUG_HIERARCHY
            dbgs() << layer << " getHierarchyTy(): #tys: " << tys->size() << "\n";
#endif
            history.pop_back();
            return tys; 
        }

        //A wrapper of getHierarchyStr() w/ a cache.
        std::set<std::string> *getTagHierarchyStr(TaintTag *tag) {
            static std::map<TaintTag*,std::set<std::string>*> cache;
            if (!tag || !tag->priv) {
                return nullptr;
            }
            if (cache.find(tag) == cache.end()) {
                std::vector<std::pair<long, AliasObject*>> history;
                history.clear();
                std::set<std::string> *strs = getHierarchyStr((AliasObject*)tag->priv, tag->fieldId, 0, history);
                cache[tag] = strs;
            }
            return cache[tag];
        }

        //A wrapper of getHierarchyTy() w/ a cache.
        std::set<std::vector<TypeField*>*> *getTagHierarchyTy(TaintTag *tag) {
            static std::map<TaintTag*,std::set<std::vector<TypeField*>*>*> cache;
            if (!tag || !tag->priv) {
                return nullptr;
            }
            if (cache.find(tag) == cache.end()) {
                std::vector<std::pair<long, AliasObject*>> history;
                history.clear();
                std::set<std::vector<TypeField*>*> *tys = getHierarchyTy((AliasObject*)tag->priv, tag->fieldId, 0, history);
                cache[tag] = tys;
            }
            return cache[tag];
        }

        bool is_prefix_hierarchy_str(std::set<std::string> *hs0, std::set<std::string> *hs1) {
            if (!hs0 || !hs1) {
                return false;
            }
            //If any string in hs0 is a string prefix (e.g. A is a prefix of AB) of any string in hs1.
            bool is_prefix = false;
            for (const std::string &s0 : *hs0) {
                for (const std::string &s1 : *hs1) {
                    //TODO: sometimes prefix and suffix may only have a sub-str overlapped (e.g. ABC and BCD).
                    if (s1.find(s0) == 0 && s0 != s1) {
                        is_prefix = true;
                        break;
                    }
                }
                if (is_prefix) {
                    break;
                }
            }
            return is_prefix;
        }

        bool is_prefix_hierarchy_ty(std::set<std::vector<TypeField*>*> *hty0, std::set<std::vector<TypeField*>*> *hty1) {
            if (!hty0 || !hty1) {
                return false;
            }
            //Get the last TypeField node in hty0.
            TypeField *tf0 = nullptr;
            for (auto &ty0 : *hty0) {
                tf0 = (*ty0)[ty0->size()-1];
                break;
            }
            if (!tf0) {
                return false;
            }
            //If the last node in hty0 is the same as any *inner* node in hty1, we say it's a prefix of hty1.
            for (auto &ty1 : *hty1) {
                for (int i = 0; i < ty1->size() - 1; ++i) {
                    TypeField *tf1 = (*ty1)[i];
                    if (tf0->is_same_ty(tf1)) {
                        return true;
                    }
                }
            }
            return false;
        }

        //Filter out those tags whose object hierarchy is a prefix of that of other tags.
        int filterTagsByHierarchy(std::set<TaintTag*> *tags) {
            if (!tags) {
                return 0;
            }
            std::set<TaintTag*> rtags;
            for (TaintTag *tag : *tags) {
                std::set<std::vector<TypeField*>*> *hty0 = getTagHierarchyTy(tag);
                if (!hty0) {
                    continue;
                }
                Type *ty0 = tag->getFieldTy();
                if (ty0 && ty0->isPointerTy()) {
                    ty0 = ty0->getPointerElementType();
                }else {
                    ty0 = nullptr;
                }
                //See whether its hierarchy is any other tag's prefix.
                bool is_prefix = false;
                for (TaintTag *t : *tags) {
                    if (t == tag) {
                        //Exclude itself.
                        continue;
                    }
                    std::set<std::vector<TypeField*>*> *hty1 = getTagHierarchyTy(t);
                    if (!hty1) {
                        continue;
                    }
                    //whether it's a prefix in the type hierarchy.
                    if (is_prefix_hierarchy_ty(hty0,hty1)) {
                        is_prefix = true;
                        break;
                    }
                    Type *ty1 = t->getTy();
                    //Sometimes it may not be the simple string prefix due to our obj hierarchy is not perfect,
                    //but we may still be able to infer the prefix by the tag type (e.g. tag1 is a pointer to tag2).
                    if (ty1 && InstructionUtils::same_types(ty0,ty1)) {
                        is_prefix = true;
                        break;
                    }
                }
                //Ok, now do an extra special filtering:
                //Dirty hack: special case: exclude file->private.
                if (!is_prefix) {
                    TypeField *tf = nullptr;
                    for (auto &e : *hty0) {
                        tf = (*e)[e->size()-1];
                    }
                    if (tf && tf->fid == 16 && dyn_cast<StructType>(tf->ty) && dyn_cast<StructType>(tf->ty)->hasName()) {
                        std::string sn = dyn_cast<StructType>(tf->ty)->getName().str();
                        InstructionUtils::trim_num_suffix(&sn);
                        if (sn == "struct.file") {
                            is_prefix = true;
                        }
                    }
                    /*
                    for (const std::string &s0 : *hs0) {
                        if (s0.find("struct.file") == 1 && s0.rfind("16") == s0.size() - 2) {
                            is_prefix = true;
                            break;
                        }
                    }
                    */
                }
                //Add to the final set if it's not a prefix.
                if (!is_prefix) {
                    rtags.insert(tag);
                }
            }
            tags->clear();
            tags->insert(rtags.begin(),rtags.end());
            return tags->size();
        }

        std::set<TaintTag*> *getAllFilteredUniqTags(Value *v) {
            static std::map<Value*,std::set<TaintTag*>> cache;
            if (!v) {
                return nullptr;
            }
            if (cache.find(v) == cache.end()) {
                for (auto const &it : taintInformation) {
                    std::map<Value*, std::set<TaintFlag*>*>* vt = it.second;
                    if (!vt || vt->size() <= 0) {
                        continue;
                    }
                    if (vt->find(v) == vt->end()) {
                        //This value doesn't exist in current context.
                        continue;
                    }
                    std::set<TaintFlag*> *tfs = (*vt)[v];
                    if (!tfs || tfs->size() <= 0) {
                        continue;
                    }
                    for (TaintFlag *p : *tfs) {
                        if (p->tag) {
                            cache[v].insert(p->tag);
                        }
                    }
                }
                //NOTE that at this point maybe cache[v] is still not inited (so cache[v] will be a null set), that's because we cannot find any taint tags for the specifed value.
                filterTagsByHierarchy(&cache[v]);
            }
            return &cache[v];
        }

        //Dump all the taint information to the raw_ostream.
        void dumpTaintInfo(llvm::raw_ostream& O) {
#ifdef DEBUG_TAINT_DUMP_PROGRESS
            unsigned long total_ctx = taintInformation.size();
            unsigned long n_ctx = 0;
#endif
            //hz: the set of the unique taint tags.
            std::set<TaintTag*> uniqTags;
            for (auto const &it : taintInformation){
#ifdef DEBUG_TAINT_DUMP_PROGRESS
                ++n_ctx;
                dbgs() << "Time for you by GuJingGong: ";
                printCurTime();
                dbgs() << n_ctx << "/" << total_ctx << " : ";
#endif
                //Does current context have any tainted values?
                std::map<Value*, std::set<TaintFlag*>*>* vt = it.second;
                if(!vt || vt->size() <= 0){
#ifdef DEBUG_TAINT_DUMP_PROGRESS
                    dbgs() << "0/0\n";
#endif
                    continue;
                }
                O << "<<<<<===============================================>>>>>\n";
                //Dump current AnalysisContext.
                it.first->printContext(O);
                //Then all the Value-TaintFlag pairs.
                O << "\n";
                unsigned long total_entry = vt->size();
                unsigned long n_entry = 0;
                for (auto const &jt : *vt) {
#ifdef DEBUG_TAINT_DUMP_PROGRESS
                    ++n_entry;
                    dbgs() << n_entry << "/" << total_entry << "..";
#endif
                    //Skip the non-branch instructions
                    if ((!dyn_cast<BranchInst>(jt.first)) && (!dyn_cast<SwitchInst>(jt.first))) {
                        continue;
                    }
                    //Dump the "Value" information.
                    O << "------------------Value------------------\n";
                    if (dyn_cast<Instruction>(jt.first)) {
                        InstructionUtils::printInst(dyn_cast<Instruction>(jt.first),O);
                    }else {
                        O << InstructionUtils::getValueStr(jt.first) << "\n";
                    }
                    //Dump the TaintFlag(s) for current value under current context.
                    std::set<TaintFlag*> *pflags = jt.second;
                    std::set<TaintTag*> *uniqVarTags = getAllFilteredUniqTags(jt.first);
                    if (!uniqVarTags) {
                        continue;
                    }
                    for (TaintFlag *p : *pflags) {
                        if (!p->tag || uniqVarTags->find(p->tag) == uniqVarTags->end()) {
                            //This means either there is no tag inf or the tag has been filtered out, so we will just skip this TaintFlag.
                            continue;
                        }
                        O << "------------------Taint------------------\n";
                        p->dumpInfo(O);
                        if (p->tag && p->tag->priv) {
                            std::set<std::string> *strs = getTagHierarchyStr(p->tag);
                            if (strs && !strs->empty()) {
                                O << "---TAG OBJ HIERARCHY---\n";
                                for (auto& hs : *strs) {
                                    O << hs << "\n";
                                }
                            }
                        }
                    }
                    uniqTags.insert(uniqVarTags->begin(),uniqVarTags->end());
                }
#ifdef DEBUG_TAINT_DUMP_PROGRESS
                dbgs() << "\n";
#endif
            }
            //Filter out some tags w/o useful information.
            for(auto it=uniqTags.begin(); it!=uniqTags.end(); ++it) {
                if (!(*it)->has_mod_insts() && !(*it)->has_cmp_consts()) {
                    uniqTags.erase(it);
                }
            }
            //Cluster the tags w/ the same type into a same group. 
            std::set<TaintTag*> uniqTags_copy = uniqTags;
            std::set<std::set<TaintTag*>> tagGroups;
            while(!uniqTags_copy.empty()) {
                TaintTag *tgt = *(uniqTags_copy.begin());
                std::set<TaintTag*> group;
                for(auto it=uniqTags_copy.begin(); it!=uniqTags_copy.end(); ++it) {
                    if (tgt->isTagEquals(*it)) {
                        group.insert(*it);
                        uniqTags_copy.erase(it);
                    }
                }
                tagGroups.insert(group);
            }
            //print the mod_inst_list of all unique taint tags.
            O << "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++\n";
            O << "+++++++++++++++++++++++MOD INST & CMP CONST LIST++++++++++++++++++++++++++\n\n";
            for (auto tag : uniqTags) {
                if (!tag->has_mod_insts() && !tag->has_cmp_consts()) {
                    continue;
                }
                O << "--------------------------TAG--------------------------\n";
                tag->dumpInfo(O);
                //print the IDs of other tags w/ the same type as this one.
                O << "===TAG GROUP: ";
                for (auto& grp : tagGroups) {
                    if (grp.find(tag) != grp.end()) {
                        for (auto& t : grp) {
                            O << static_cast<const void *>(t) << ", ";
                        }
                    }
                }
                O << "\n";
                //Mod insts of this tag.
                if (tag->has_mod_insts()) {
                    tag->printModInsts(O,&(this->switchMap));
                }
                //Cmp consts of this tag.
                if (tag->has_cmp_consts()) {
                    tag->printCmpConsts(O);
                }
            }
            O << "++++++++++++++++++++++++Br Traits+++++++++++++++++++++++++++\n";
            for (auto& x : this->brTraitMap) {
                O << "-----------Br-----------\n";
                O << InstructionUtils::getValueStr(x.first) << "\n";
                O << "-----------Traits (one line per ctx)-----------\n";
                for (auto& y : x.second) {
                    //y.first -> ctx*
                    for (auto& z : y.second) {
                        O << z.first << ":" << z.second << " ";
                    }
                    O << "\n";
                }
            }
            O << "++++++++++++++++++++++++Mod Traits+++++++++++++++++++++++++++\n";
            for (auto& x : this->modTraitMap) {
                O << "-----------Mod-----------\n";
                O << InstructionUtils::getValueStr(x.first) << "\n";
                O << "-----------Traits (one line per ctx)-----------\n";
                for (auto& y : x.second) {
                    //y.first -> ctx*
                    for (auto& z : y.second) {
                        O << z.first << ":" << z.second << " ";
                    }
                    O << "\n";
                }
            }
            return;
        }

        void serializeTaintInfo(std::string fn) {
            //Store taint information in a map as below and then serialize it.
            TAINTED_BR_TY taintedBrs;
            CTX_MAP_TY ctxMap;
            INST_TRAIT_MAP traitMap;
            //hz: the set of the unique taint tags.
            std::set<TaintTag*> uniqTags;
#ifdef DEBUG_TAINT_SERIALIZE_PROGRESS
            dbgs() << "Serialize information about tainted branch IR...\n";
            int a_ctx_cnt = 0;
            int total_a_ctx = taintInformation.size();
#endif
            for (auto const &it : taintInformation){
                //Does current context have any tainted values?
#ifdef DEBUG_TAINT_SERIALIZE_PROGRESS
                dbgs() << "Analysis Ctx " << (++a_ctx_cnt)  << "/" << total_a_ctx << ":\n";
                int br_cnt = 0;
#endif
                std::map<Value *, std::set<TaintFlag*>*>* vt = it.second;
                if(!vt || vt->size() <= 0){
                    continue;
                }
                //it.first is AnalysisContext*
                ID_TY ctx_id = (ID_TY)(it.first->callSites);
                //Then all the Value-TaintFlag pairs.
                bool any_br_taint = false;
                for (auto const &jt : *vt){
                    //Serialize the "Value" information.
                    //Only care about the branch instruction (e.g. br, switch)
                    if ((!dyn_cast<BranchInst>(jt.first)) && (!dyn_cast<SwitchInst>(jt.first))) {
                        continue;
                    }
                    BranchInst *br_inst = dyn_cast<BranchInst>(jt.first);
#ifdef DEBUG_TAINT_SERIALIZE_PROGRESS
                    dbgs() << (++br_cnt) << " ";
#endif
                    //NOTE: TaintTag represents the taint src,
                    //TaintFlag provides the path by which the taint src can taint current inst.
                    //TODO: utilize the path inf in TaintFlag to filter out some 'store' insts (e.g. write after read) 
                    std::set<TaintFlag*> *pflags = jt.second;
                    if ((!pflags) || pflags->empty()) {
                        continue;
                    }
                    any_br_taint = true;
                    LOC_INF *p_str_inst = InstructionUtils::getInstStrRep(dyn_cast<Instruction>(jt.first));
                    //Here we assume that the branch instruction is always the last instruction of a BB so that one BB -> one branch inst.
                    BR_INF *p_br_inf = &(taintedBrs[(*p_str_inst)[3]][(*p_str_inst)[2]][(*p_str_inst)[1]]);
                    //Get the br instruction trait if any.
                    if (br_inst &&
                            this->brTraitMap.find(br_inst) != this->brTraitMap.end() && 
                            this->brTraitMap[br_inst].find(it.first->callSites) != this->brTraitMap[br_inst].end())
                    {
                        TRAIT *p_trait = &(this->brTraitMap[br_inst][it.first->callSites]);
                        traitMap[(ID_TY)p_trait] = *p_trait;
                        //Set the trait id
                        std::get<0>((*p_br_inf)[ctx_id]) = (ID_TY)p_trait;
                    }else{
                        //No trait, so set an invalid trait ID.
                        std::get<0>((*p_br_inf)[ctx_id]) = 0;
                    }
                    //Get and filter the TaintTags that taint current inst.
                    std::set<TaintTag*> *uniqVarTags = getAllFilteredUniqTags(jt.first);
                    if (!uniqVarTags) {
                        continue;
                    }
                    for (TaintFlag *p : *pflags) {
                        if (!p || !p->tag || uniqVarTags->find(p->tag) == uniqVarTags->end()) {
                            continue;
                        }
                        //Add the tag id
                        std::get<1>((*p_br_inf)[ctx_id]).insert((ID_TY)(p->tag));
                        uniqTags.insert(p->tag);
                    }
                }
                if (any_br_taint) {
                    //Record current AnalysisContext.
                    std::vector<LOC_INF> *pctx = InstructionUtils::getStrCtx(it.first->callSites);
                    ctxMap[ctx_id] = *pctx;
                }
#ifdef DEBUG_TAINT_SERIALIZE_PROGRESS
                dbgs() << "\n";
#endif
            }
            //Ok, now store all uniq TaintTags in a map.
            TAG_INFO_TY tagInfoMap;
            TAG_MOD_MAP_TY tagModMap;
            TAG_CONST_MAP_TY tagConstMap;
#ifdef DEBUG_TAINT_SERIALIZE_PROGRESS
            dbgs() << "Serialize information about taint tags and modification IRs...\n";
            int tag_cnt = 0;
            int total_tag_cnt = uniqTags.size();
#endif
            for (TaintTag *tag : uniqTags) {
#ifdef DEBUG_TAINT_SERIALIZE_PROGRESS
                dbgs() << (++tag_cnt) << "/" << total_tag_cnt << "\n";
#endif
                ID_TY tag_id = (ID_TY)tag;
                const std::string& ty_str = tag->getTypeStr();
                tagInfoMap[tag_id]["ty"] = ty_str;
                tagInfoMap[tag_id]["is_global"] = (tag->is_global ? "true" : "false");
                tagInfoMap[tag_id]["field"] = std::to_string(tag->fieldId);
                tagInfoMap[tag_id]["v"] = InstructionUtils::getValueStr(tag->v);
                tagInfoMap[tag_id]["vid"] = std::to_string((unsigned long)(tag->v));
                if (tag->priv) {
                    std::set<std::string> *hstrs = getTagHierarchyStr(tag);
                    if (hstrs && !hstrs->empty()) {
                        int hc = 0;
                        for (auto& hs : *hstrs) {
                            tagInfoMap[tag_id]["hs_" + std::to_string(hc)] = hs;
                            ++hc;
                        }
                    }
                }
                //Record cmp constants of tags.
                for (auto& e : tag->cmp_constants) {
                    LOC_INF *p_str_inst = InstructionUtils::getInstStrRep(e.first);
                    if (!p_str_inst || e.second.empty()) {
                        continue;
                    }
                    tagConstMap[tag_id][(*p_str_inst)[3]][(*p_str_inst)[2]][(*p_str_inst)[1]][(*p_str_inst)[0]] = e.second;
                }
                //Record mod insts of the tag.
                for (auto& e : tag->mod_insts) {
                    LOC_INF *p_str_inst = InstructionUtils::getInstStrRep(e.first);
                    StoreInst *st_inst = dyn_cast<StoreInst>(e.first);
                    //Iterate over the ctx of the mod inst.
                    for (auto ctx : e.second) {
                        //"ctx" is of type "std::vector<Instruction*>*".
                        ID_TY ctx_id = (ID_TY)ctx;
                        std::vector<LOC_INF> *pctx = InstructionUtils::getStrCtx(ctx);
                        ctxMap[ctx_id] = *pctx;
                        CONSTRAINTS *p_constraints;
                        p_constraints = &(tagModMap[tag_id][(*p_str_inst)[3]][(*p_str_inst)[2]][(*p_str_inst)[1]][(*p_str_inst)[0]][ctx_id]);
                        //Fill in the mod inst traits if any.
                        if (this->modTraitMap.find(st_inst) != this->modTraitMap.end() && 
                                this->modTraitMap[st_inst].find(ctx) != this->modTraitMap[st_inst].end())
                        {
                            TRAIT *p_trait = &(this->modTraitMap[st_inst][ctx]);
                            traitMap[(ID_TY)p_trait] = *p_trait;
                            //Set the trait id
                            (*p_constraints)[TRAIT_INDEX].insert((ID_TY)p_trait);
                        }
                        //Fill in the constraints of func args if any.
                        std::set<uint64_t> *p_cmds = InstructionUtils::getCmdValues(ctx,e.first,&(this->switchMap));
                        if (!p_cmds) {
                            continue;
                        }
                        //TODO: we now simply assume that "cmd" is the 2nd arg of entry ioctl.
                        (*p_constraints)[1] = *p_cmds;
                    }
                }
            }
            //Serialize the calleeMap.
            CALLEE_MAP_TY calleeInfMap;
            for (auto& x : this->calleeMap) {
                //x.first is the callee function name
                for (auto& y : x.second) {
                    //y.first is CallInst*
                    LOC_INF *p_str_inst = InstructionUtils::getInstStrRep(y.first);
                    if (!p_str_inst) {
                        continue;
                    }
                    //y.second is set<ctx*>
                    for (auto& ctx : y.second) {
                        ID_TY ctx_id = (ID_TY)ctx;
                        std::vector<LOC_INF> *pctx = InstructionUtils::getStrCtx(ctx);
                        ctxMap[ctx_id] = *pctx;
                        CONSTRAINTS *p_constraints = &(calleeInfMap[x.first][(*p_str_inst)[3]][(*p_str_inst)[2]][(*p_str_inst)[1]][(*p_str_inst)[0]][ctx_id]);
                        std::set<uint64_t> *p_cmds = InstructionUtils::getCmdValues(ctx,y.first,&(this->switchMap));
                        if (!p_cmds) {
                            continue;
                        }
                        //TODO: we now simply assume that "cmd" is the 2nd arg of entry ioctl.
                        (*p_constraints)[1] = *p_cmds;
                    }
                }
            }
#ifdef DEBUG_TAINT_SERIALIZE_PROGRESS
            dbgs() << "Serialize to file...\n";
#endif
            /*
            //Serialize all data structures with cereal.
            std::ofstream outfile;
            outfile.open(fn);
            {
            cereal::XMLOutputArchive oarchive(outfile);
            oarchive(taintedBrs, analysisCtxMap, tagModMap, tagInfoMap, modInstCtxMap);
            }//archive goes out of scope, ensuring all contents are flushed.
            outfile.close();
             */
            //Use "json for C++" to serialize...
            std::ofstream outfile;
            outfile.open(fn);

            json j_taintedBrs(taintedBrs);
            json j_ctxMap(ctxMap);
            json j_traitMap(traitMap);
            json j_tagModMap(tagModMap);
            json j_tagConstMap(tagConstMap);
            json j_tagInfoMap(tagInfoMap);
            json j_calleeInfMap(calleeInfMap);

            outfile << j_taintedBrs << j_ctxMap << j_traitMap << j_tagModMap << j_tagConstMap << j_tagInfoMap << j_calleeInfMap;
            outfile.close();
#ifdef DEBUG_TAINT_SERIALIZE_PROGRESS
            dbgs() << "Serialization finished!\n";
#endif
        }

        void printCurTime() {
            auto t_now = std::chrono::system_clock::now();
            std::time_t now_time = std::chrono::system_clock::to_time_t(t_now);
            dbgs() << std::ctime(&now_time) << "\n";
        }

        // Range analysis helpers

        /***
         * Get range for the provided value
         * @param targetValue Value for which range needs to be fetched.
         * @return Pointer to range object, if exists, else Null.
         */
        RangeAnalysis::Range getRange(Value *targetValue) {
            return this->range_analysis->getRange(targetValue);
        }

        // Adding vulnerability warning

        /***
         * Add the provided vulnerability warning to the current state indexed by instruction.
         * @param currWarning Vulnerability warning that needs to be added.
         */
        void addVulnerabilityWarningByInstr(VulnerabilityWarning *currWarning) {
            Instruction *targetInstr = currWarning->target_instr;
            std::set<VulnerabilityWarning*> *warningList = nullptr;
            if(warningsByInstr.find(targetInstr) == warningsByInstr.end()) {
                warningsByInstr[targetInstr] = new std::set<VulnerabilityWarning*>();
            }
            warningList = warningsByInstr[targetInstr];

            for(auto a:*warningList) {
                if(a->isSameVulWarning(currWarning)) {
                    return;
                }
            }
            warningList->insert(currWarning);
        }

        /***
         * Add the provided vulnerability warning to the current state.
         * @param currWarning Vulnerability warning that needs to be added.
         */
        void addVulnerabilityWarning(VulnerabilityWarning *currWarning) {
            assert(currWarning != nullptr);
            AnalysisContext* currContext = getContext(currWarning->getCallSiteTrace());
            assert(currContext != nullptr);
            if(allVulnWarnings.find(currContext) == allVulnWarnings.end()) {
                // first vulnerability warning.
                allVulnWarnings[currContext] = new std::set<VulnerabilityWarning*>();
            }
            allVulnWarnings[currContext]->insert(currWarning);

            this->addVulnerabilityWarningByInstr(currWarning);

        }
    };
}

#endif //PROJECT_MODULESTATE_H
