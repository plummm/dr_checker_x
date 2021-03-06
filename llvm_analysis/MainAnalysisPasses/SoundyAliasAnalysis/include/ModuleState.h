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
#include "../../Utils/include/CFGUtils.h"
#include "../../Utils/include/Constraint.h"

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
#define DEBUG_HIERARCHY
#define DEBUG_CONSTRUCT_TAINT_CHAIN

using namespace llvm;

namespace DRCHECKER {


    struct callsiteinfo{
        std::string funcname;
        Function* func;
        std::string filename;
        int linenum;
        bool isInline;
    };
//#define DEBUG_GLOBALS
    /***
     * Class that abstracts the context.
     * Definition 3.5 of the paper.
     */
    class AnalysisContext {
    public:
        std::vector<Instruction *> *callSites;
        void printContext(llvm::raw_ostream& O) {
            O << "------------CONTEXT------------\n";
            if (!callSites) {
                O << "Null this->callSites!!\n";
            }else {
                int no = 0;
                for(Instruction *currCallSite : *(this->callSites)) {
                    O << no << " ";
                    InstructionUtils::printInst(currCallSite,O);
                    ++no;
                }
            }
            O << "-------------------------------\n";
        }

        void printContextJson(llvm::raw_ostream& O) {
            O << "\"context\":[";
            bool putComma = false;
            if (this->callSites) {
                for(Instruction *currCallSite : *(this->callSites)) {
                    if(putComma) {
                        O << ",";
                    }
                    O << "{";
                    InstructionUtils::printInstJson(currCallSite,O);
                    O << "}\n";
                    putComma = true;
                }
            }
            O << "\n]";
        }
    };

    static std::set<std::vector<TypeField*>*> htys;
    static std::set<std::string> hstrs;
    static std::set<std::set<AliasObject*>*> eqObjs;

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
        std::map<AnalysisContext*, std::map<Value*, std::set<PointerPointsTo*>*>*> pointToInformation;

        static std::map<Value *, std::set<PointerPointsTo*>*> globalVariables;

        static std::map<Function*, std::set<BasicBlock*>*> loopExitBlocks;

        // Data layout for the current module
        DataLayout *targetDataLayout;

        // Information needed for TaintAnalysis
        std::map<AnalysisContext*, std::map<Value*, std::set<TaintFlag*>*>*> taintInformation;

        // Store the value constraints imposed by different paths.
        std::map<AnalysisContext*, std::map<Value*, Constraint*>> constraintInformation;

        // These are the infeasible (due to conflicting path constraints) basic blocks under each calling context.
        std::map<AnalysisContext*, std::set<BasicBlock*>> deadBBs;

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

        //Indicates the analysis phase we're currently in, now:
        //1 = preliminary phase, 2 = main analysis phase, 3 = bug detection phase.
        int analysis_phase = 0;

        //Current interesting value
        Value* basePointer;
        int offsetfrbase;
        Function* entryfunc;
        Instruction* interestinginst;
        bool taintedAllTarget = false;

        std::set<Instruction *> visitedsites;

        std::map<Instruction *, std::set<Value *>> baseptrmap;

        int filecounter;

        std::vector<callsiteinfo*> callsiteinfos;

        std::set<Instruction*> topcallsites;

        int calltracepointer;
        int calltracebasepointer;

        std::vector<Instruction *>vulsitecontext;

        std::map<Value *, int> offset4baseptrs;

        std::set<CallInst *> taintedindirectcalls;

        std::string printPathDir;

        //std::vector<CalltraceItem*> syzcalltrace;


        GlobalState(DataLayout *currDataLayout) {
            //this->range_analysis = ra;
            this->targetDataLayout = currDataLayout;
        }

        ~GlobalState() {
            //cleanup();

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
            // Even stripping din't help. Check if this is an instruction and get the first
            // global variable in operand list
            // TODO: a better handling of the ConstantExpr. 
            if (actualGlobal == nullptr && dyn_cast<ConstantExpr>(currVal)) {
                ConstantExpr *targetExpr = dyn_cast<ConstantExpr>(currVal);
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
                    AliasObject *refObj = getReferencedGlobal(visitedCache, currOperand, globalObjectCache);
                    if(refObj != nullptr) {
                        return refObj;
                    }
                }
            }
            //Is it a function?
            if (actualGlobal == nullptr && dyn_cast<Function>(currVal)) {
                Function *targetFunction = dyn_cast<Function>(currVal);
                //NOTE: we assume that all functions that have definitions in the module have already 
                //been added to globalObjectCache (i.e. in "setupGlobals").
                if (globalObjectCache.find((Value*)targetFunction) != globalObjectCache.end()) {
                    return globalObjectCache[(Value*)targetFunction];
                }else {
                    // dbgs() << "!!! getReferencedGlobal(): Cannot find the targetFunction in the cache: "
                    // << targetFunction->getName().str() << "\n";
                }
            }
            if(actualGlobal != nullptr) {
                //Not a function, neither expr, it's a normal global object pointer.
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
                                                           Constant *targetConstant,
                                                           std::map<Value*, AliasObject*> &globalObjectCache) {
            if (!targetConstant || !targetConstant->getType() || !dyn_cast<ConstantAggregate>(targetConstant)) {
                return nullptr;
            }
            ConstantAggregate *constA = dyn_cast<ConstantAggregate>(targetConstant);
            Type* constantType = targetConstant->getType();
            AliasObject *glob = new GlobalObject(targetConstant, constantType);
            //hz: this can handle both the struct and sequential type.
            for (unsigned int i = 0; i < constA->getNumOperands(); ++i) {
                Constant *constCheck = constA->getOperand(i);
                if (!constCheck) {
                    continue;
                }
                AliasObject *currFieldObj = nullptr;
                if (isConstantVariable(constCheck)) {
                    // OK, the field is initialized w/ a global object pointer, now get that pointee global object.
                    currFieldObj = getReferencedGlobal(visitedCache, constCheck, globalObjectCache);
                    //Update the field point-to record.
                    if (currFieldObj != nullptr) {
                        //Since this is the global object initialization, the InstLoc is nullptr.
                        glob->addObjectToFieldPointsTo(i, currFieldObj, nullptr);
                    }
                } else if (dyn_cast<ConstantAggregate>(constCheck)) {
                    // This is an embedded struct...
                    currFieldObj = getGlobalObjectFromInitializer(visitedCache, constCheck, globalObjectCache);
                    // Update the embed object record.
                    if (currFieldObj != nullptr) {
                        glob->setEmbObj(i, currFieldObj, true);
                    }
                } else {
                    // This is possibly an integer field initialization, we can just skip.
                    continue; 
                }
            }
            return glob;
        }

        //Decide whether we need to create a GlobalObject for a certain GlobalVariable.
        static bool toCreateObjForGV(llvm::GlobalVariable *globalVariable) {
            if (!globalVariable) {
                return false;
            }
            Type *ty = globalVariable->getType();
            // global variables are always pointers
            if (!ty || !ty->isPointerTy()) {
                return false;
            }
            ty = ty->getPointerElementType();
            // Don't create GlobalObject for certain types (e.g. str pointer). 
            if (dyn_cast<SequentialType>(ty)) {
                Type *ety = dyn_cast<SequentialType>(ty)->getElementType();
                if (InstructionUtils::isPrimitiveTy(ety) || InstructionUtils::isPrimitivePtr(ety)) {
                    return false;
                }
            }
            //Filter by name.
            std::string bls[] = {".str.",".descriptor"};
            if (globalVariable->hasName()) {
                std::string n = globalVariable->getName().str();
                for (auto &s : bls) {
                    if (s == n) {
                        return false;
                    }
                }
            }
            return true;
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
        static AliasObject* addGlobalVariable(std::vector<llvm::GlobalVariable*> &visitedCache,
                                              llvm::GlobalVariable *globalVariable,
                                      std::map<Value*, AliasObject*> &globalObjectCache) {

            if (!globalVariable) {
                return nullptr;
            }
            if(std::find(visitedCache.begin(), visitedCache.end(), globalVariable) != visitedCache.end()) {
#ifdef DEBUG_GLOBALS
                dbgs() << "Cycle Detected for: " << InstructionUtils::getValueStr(globalVariable) << "\n";
#endif
                return nullptr;
            }
            Value *objectCacheKey = dyn_cast<Value>(globalVariable);
            Type *baseType = globalVariable->getType();
            // global variables are always pointers
            if (!baseType || !baseType->isPointerTy()) {
                return nullptr;
            }
            Type *objType = baseType->getPointerElementType();
            //Don't create the GlobalObject for certain GVs.
            if (!toCreateObjForGV(globalVariable)) {
                return nullptr;
            }
            // if its already processed? Return previously created object.
            if(globalObjectCache.find(objectCacheKey) != globalObjectCache.end()) {
                return globalObjectCache[objectCacheKey];
            }
            AliasObject *toRet = nullptr;
            visitedCache.push_back(globalVariable);
            // This is new global variable.
            // next check if it has any initializers.
            if (globalVariable->hasInitializer()) {
                Constant *targetConstant = globalVariable->getInitializer();
                toRet = getGlobalObjectFromInitializer(visitedCache, targetConstant, globalObjectCache);
            }
            if(toRet == nullptr) {
                // OK, the global variable has no initializer.
                // Just create a default object.
                toRet = new GlobalObject(globalVariable, objType);
            }
            //Update the global pto records.
            if (toRet != nullptr) {
                //TODO: confirm that the global variable is const equals to the pointee object is also const.
                toRet->is_const = globalVariable->isConstant();
                //hz: since this is the pre-set pto for gv, there is no calling context. 
                std::set<PointerPointsTo*> *newPointsTo = new std::set<PointerPointsTo*>();
                PointerPointsTo *pointsToObj = new PointerPointsTo(globalVariable, toRet, 0, new InstLoc(globalVariable,nullptr), false);
                newPointsTo->insert(newPointsTo->end(), pointsToObj);
                assert(GlobalState::globalVariables.find(globalVariable) == GlobalState::globalVariables.end());
                GlobalState::globalVariables[globalVariable] = newPointsTo;
                //dbgs() << "Adding:" << *globalVariable << " into cache\n";
                // make sure that object cache doesn't already contain the object.
                assert(globalObjectCache.find(objectCacheKey) == globalObjectCache.end());
                // insert into object cache.
                globalObjectCache[objectCacheKey] = toRet;
                // Make sure that we have created a pointsTo information for globals.
                assert(GlobalState::globalVariables.find(globalVariable) != GlobalState::globalVariables.end());
                assert(GlobalState::globalVariables[globalVariable] != nullptr);
            }
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
                std::set<PointerPointsTo*> *newPointsTo = new std::set<PointerPointsTo*>();
                GlobalObject *glob = new GlobalObject(currFunction);
                PointerPointsTo *pointsToObj = new PointerPointsTo(currFunction, glob, 0, new InstLoc(currFunction,nullptr), false);
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
        AnalysisContext* getContext(std::vector<Instruction*> *callSites) {
            if (!callSites || callSites->empty()) {
                if (this->analysis_phase > 2) {
                    dbgs() << "!!! getContext(): Null callSites received in the bug detection phase!\n";
                }
                return nullptr;
            }
            for (auto curr_a : availableAnalysisContexts) {
                if(*(curr_a->callSites) == *callSites) {
                    return curr_a;
                }
            }
            //////////Below is just for debugging...
            //In theory all contexts have been analyzed in the main analysis phase, it's impossible that
            //in bug detection phase we have an unseen context. If this happens, we really need a thorough inspection...
            if (this->analysis_phase > 2) {
                dbgs() << "!!!!! getContext(): In bug detection phase we have an unseen calling context:\n";
                for (Instruction *inst : *callSites) {
                    InstructionUtils::printInst(inst,dbgs());
                }
                dbgs() << "We now have " << this->availableAnalysisContexts.size() << " ctx available, try to find a nearest one...\n";
                //(1) Longest common prefix, and (2) most matched insts.
                std::vector<Instruction*> *lcp = nullptr, *mmi = nullptr;
                int nlcp = 0, nmmi = 0;
                for (auto curr_a : this->availableAnalysisContexts) {
                    std::vector<Instruction*> *c = curr_a->callSites;
                    if (!c) {
                        continue;
                    }
                    bool pr = true;
                    int nl = 0, nm = 0;
                    for (int i = 0; i < callSites->size() && i < c->size(); ++i) {
                        if ((*c)[i] == (*callSites)[i]) {
                            if (pr) {
                                ++nl;
                            }
                            ++nm;
                        }else {
                            pr = false;
                        }
                    }
                    if (nl > nlcp) {
                        nlcp = nl;
                        lcp = c;
                    }
                    if (nm > nmmi) {
                        nmmi = nm;
                        mmi = c;
                    }
                }
                if (lcp) {
                    dbgs() << "==The candidate w/ longest common prefix:\n";
                    for (Instruction *inst : *lcp) {
                        InstructionUtils::printInst(inst,dbgs());
                    }
                }
                if (mmi) {
                    dbgs() << "==The candidate w/ most matched insts:\n";
                    for (Instruction *inst : *mmi) {
                        InstructionUtils::printInst(inst,dbgs());
                    }
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
        AnalysisContext* getOrCreateContext(std::vector<Instruction*> *callSites, std::map<Value*,
                std::set<PointerPointsTo*>*> *targetInfo = nullptr, std::map<Value *, std::set<TaintFlag*>*> *targetTaintInfo = nullptr) {

            AnalysisContext* currContext = getContext(callSites);
            if(currContext == nullptr) {
                // Create a new context for the provided instruction with provided points to info.
                AnalysisContext *newContext = new AnalysisContext();
                newContext->callSites = callSites;
                // insert the new context into available contexts.
                availableAnalysisContexts.insert(availableAnalysisContexts.end(), newContext);

                // create new points to information.
                std::map<Value*, std::set<PointerPointsTo*>*> *newInfo = new std::map<Value*, std::set<PointerPointsTo*>*>();
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
            return pointToInformation[currContext];
        }

        std::map<Value*, Constraint*> *getCtxConstraints(std::vector<Instruction*> *callSites) {
            if (!callSites) {
                return nullptr;
            }
            AnalysisContext* currContext = getContext(callSites);
            assert(currContext);
            return &(this->constraintInformation[currContext]);
        }

        Constraint *getConstraints(std::vector<Instruction*> *callSites, Value *v, bool create = true) {
            if (!callSites || callSites->empty() || !v) {
                return nullptr;
            }
            AnalysisContext* currContext = getContext(callSites);
            assert(currContext);
            if (this->constraintInformation.find(currContext) != this->constraintInformation.end() &&
                this->constraintInformation[currContext].find(v) != this->constraintInformation[currContext].end()) {
                Constraint *r = this->constraintInformation[currContext][v];
                if (r) {
                    //Got the existing Constraint.
                    return r;
                }
            }
            //This means there is no existing constraint, create one if specified.
            if (create) {
                Instruction *i = (*callSites)[callSites->size()-1];
                Function *f = nullptr;
                if (i && i->getParent()) {
                    f = i->getParent()->getParent();
                }
                Constraint *r = new Constraint(v,f);
                this->constraintInformation[currContext][v] = r;
                return r;
            }
            return nullptr;
        }

        bool setConstraints(std::vector<Instruction*> *callSites, Value *v, Constraint *c) {
            if (!callSites || !v || !c) {
                return false;
            }
            AnalysisContext* currContext = getContext(callSites);
            assert(currContext);
            this->constraintInformation[currContext][v] = c;
            return true;
        }

        //Insert the provided dead BBs to the current records.
        void updateDeadBBs(std::vector<Instruction*> *callSites, std::set<BasicBlock*> &bbs) {
            if (!callSites || callSites->empty() || bbs.empty()) {
                return;
            }
            AnalysisContext* currContext = getContext(callSites);
            assert(currContext);
            (this->deadBBs)[currContext].insert(bbs.begin(),bbs.end());
            return;
        }

        std::set<BasicBlock*> *getDeadBBs(std::vector<Instruction*> *callSites) {
            if (!callSites || callSites->empty()) {
                return nullptr;
            }
            AnalysisContext* currContext = getContext(callSites);
            assert(currContext);
            if (this->deadBBs.find(currContext) != this->deadBBs.end()) {
                return &((this->deadBBs)[currContext]);
            }
            return nullptr;
        }

        bool isDeadBB(std::vector<Instruction*> *callSites, BasicBlock *bb) {
            std::set<BasicBlock*> *dbbs = this->getDeadBBs(callSites);
            if (!dbbs || !bb) {
                return false;
            }
            return (dbbs->find(bb) != dbbs->end());
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

        //The standard is whether the obj/field combination exists in the history, nothing to do w/ TaintFlag.
        bool in_taint_history(TypeField *tf, std::vector<TypeField*> &history, bool insert = false) {
            if (!tf) {
                return true;
            }
            for (TypeField *htf : history) {
                if (!htf) {
                    continue;
                }
                if (htf->fid == tf->fid && 
                    (htf->priv == tf->priv || isEqvObj((AliasObject*)(htf->priv),(AliasObject*)(tf->priv)) > 0)) 
                {
                    return true;
                }
            }
            if (insert) {
                history.push_back(tf);
            }
            return false;
        }

        bool insertTaintPath(std::vector<InstLoc*> *tr, std::set<std::vector<InstLoc*>*> &res) {
            if (!tr) {
                return false;
            }
            if (res.size() > 1024) {
                //Already too many taint paths, to avoid explosion, skip.
                return false;
            }
            //If no duplication, insert.
            for (auto t : res) {
                if (DRCHECKER::sameLocTr(t,tr)) {
                    return false;
                }
            }
            res.insert(tr);
            return true;
        }

        bool insertTaintPath(std::vector<TypeField*> &chain, std::set<std::vector<InstLoc*>*> &res) {
            if (chain.empty()) {
                return false;
            }
            if (res.size() > 1024) {
                //Already too many taint paths, to avoid explosion, skip.
                return false;
            }
            std::set<std::vector<InstLoc*>*> ps,tmp;
            ps.insert(new std::vector<InstLoc*>());
            for (int i = chain.size() - 1; i > 0; --i) {
                TypeField *tf = chain[i];
                if (!tf || tf->tfs.empty()) {
                    continue;
                }
                if (tf->tfs.size() > 1) {
                    //More than one taint paths for the current link.
                    //Option 0: Select a shortest path (current choice)
                    TaintFlag *stf = nullptr;
                    for (void *pt : tf->tfs) {
                        if (!pt) {
                            continue;
                        }
                        TaintFlag *tflg = (TaintFlag*)pt;
                        if (!stf || tflg->instructionTrace.size() < stf->instructionTrace.size()) {
                            stf = tflg;
                        }
                    }
                    if (stf) {
                        for (std::vector<InstLoc*> *p : ps) {
                            //TODO: any cross-entry-func taint path validity test?
                            p->insert(p->end(),stf->instructionTrace.begin(),stf->instructionTrace.end());
                        }
                    }
                    //Option 1: Insert all
                    /*
                    tmp.clear();
                    for (std::vector<InstLoc*> *p : ps) {
                        for (void *pt : tf->tfs) {
                            TaintFlag *tflg = (TaintFlag*)pt;
                            std::vector<InstLoc*> *np = new std::vector<InstLoc*>(*p);
                            //TODO: any cross-entry-func taint path validity test?
                            np->insert(np->end(),tflg->instructionTrace.begin(),tflg->instructionTrace.end());
                            tmp.insert(np);
                        }
                    }
                    ps.clear();
                    ps = tmp;
                    */
                }else {
                    TaintFlag *tflg = (TaintFlag*)(*(tf->tfs.begin()));
                    for (std::vector<InstLoc*> *p : ps) {
                        //TODO: any cross-entry-func taint path validity test?
                        p->insert(p->end(),tflg->instructionTrace.begin(),tflg->instructionTrace.end());
                    }
                }
            }
            //Now insert the paths to the res set.
            for (std::vector<InstLoc*> *p : ps) {
                if (!insertTaintPath(p,res)) {
                    delete(p);
                }
            }
            return true;
        }

        //Decide whether we need to give up searching the taint paths due to the path explosion.
        //Arg: "np": #path already searched; "ntp": #taintPath already found
        bool valid_taint_history(std::vector<TypeField*> &history, int np, int ntp) {
            if (np > 10240) {
                //There are really too many searched paths, so restrict the search to a low level.
                if (history.size() > 4) {
                    return false;
                }
            }
            if (history.size() < 8) {
                return true;
            }
            if (ntp > 0) {
                //At least one user taint path has already been identified, so we can give up here.
                return false;
            }
            if (np > 1024) {
                //Though we haven't found any taint paths, there are already too many paths searched,
                //to avoid explosion, we'd better stop the search.
                return false;
            }
            return true;
        }

        //Return all taint paths from the user input to the specified field of an object.
        //NOTE: we assume that "res" is empty and there is no TF in "tf" when invoking this function at layer 0.
        int getAllUserTaintPaths(TypeField *tf, std::vector<TypeField*> &history, std::set<std::vector<InstLoc*>*> &res) {
            //obj -> fid -> user taint path to this specific field in the obj.
            static std::map<AliasObject*, std::map<long, std::set<std::vector<InstLoc*>*>>> pathMap;
            static int cnt_sp = 0;
            if (history.empty()) {
                //Root node (i.e. layer 0), reset the counter for #path searched.
                cnt_sp = 0;
            }
            if (!tf || !tf->priv) {
                return 0;
            }
            AliasObject *obj = (AliasObject*)(tf->priv);
            long fid = tf->fid;
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
            dbgs() << "getAllUserTaintPaths(): #history " << history.size() << ": Get taint paths for " 
            << (const void*)obj << "|" << fid << "\n"; 
#endif
            //Ok, see whether the result has already been cached.
            if (pathMap.find(obj) != pathMap.end() && pathMap[obj].find(fid) != pathMap[obj].end()) {
                //Anyway we will return directly here and stop searching along this path, so increase the counter.
                ++cnt_sp;
                //Cached, return directly w/ path concat.
                if (pathMap[obj][fid].empty()) {
                    return 0;
                }
                std::set<std::vector<InstLoc*>*> hps;
                history.push_back(tf);
                insertTaintPath(history,hps);
                history.pop_back();
                if (hps.empty()) {
                    return 0;
                }
                for (std::vector<InstLoc*> *tr : pathMap[obj][fid]) {
                    if (!tr) {
                        continue;
                    }
                    for (std::vector<InstLoc*> *hp : hps) {
                        if (!hp) {
                            continue;
                        }
                        std::vector<InstLoc*> *np = new std::vector<InstLoc*>(*tr);
                        np->insert(np->end(),hp->begin(),hp->end());
                        if (!insertTaintPath(np,res)) {
                            delete(np);
                        }
                    }
                }
                return pathMap[obj][fid].size();
            }
            if (this->in_taint_history(tf,history,true)) {
                //A taint loop, stop here.
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                dbgs() << "getAllUserTaintPaths(): loop detected, return!\n";
#endif
                ++cnt_sp;
                return 0;
            }
            if (!this->valid_taint_history(history,cnt_sp,res.size())) {
                //Stop searching to avoid the taint path explosion.
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                dbgs() << "getAllUserTaintPaths(): too many taint paths, stop here...\n";
#endif
                history.pop_back();
                ++cnt_sp;
                return 0;
            }
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
            dbgs() << "getAllUserTaintPaths(): no result in cache, do the search!\n";
#endif
            //Find out who can taint this obj/field...
            //First get all eqv objects to the current one.
            std::set<AliasObject*> eqObjs;
            getAllEquivelantObjs(obj,eqObjs);
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
            dbgs() << "getAllUserTaintPaths(): Got " << eqObjs.size() << " eqv objs: ";
            for (AliasObject *o : eqObjs) {
                dbgs() << (const void*)o << " ";
            }
            dbgs() << "\n";
#endif
            //We need to consider all possible taints to every eqv object...
            std::map<AliasObject*,std::map<long,std::set<TaintFlag*>>> wtfs;
            for (AliasObject *o : eqObjs) {
                if (!o) {
                    continue;
                }
                //Ok, who can taint this obj|field?
                //TODO: if the original arg tf->priv is different than the current eqv obj "o", the bug analyst may be
                //confused about how "tf->priv" can be controlled by the user... Consider what we can do to help.
                //NOTE: now we only consider the taint paths valid in the single-thread execution setting (e.g. one TF may be masked by another
                //during the execution, in which case we only consider the TF that can last to the function return).
                //TODO: try to detect the concurrency bugs (e.g. just before a TF is masked in one entry, we can invoke another entry function 
                //in which the obj|field still bear the effect of that TF...)
                std::set<TaintFlag*> tflgs;
                o->getWinnerTfs(fid,tflgs);
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                dbgs() << "getAllUserTaintPaths(): eqv obj " << (const void*)o << " has #winnerTFs: " << tflgs.size() << "\n";
#endif
                for (TaintFlag *flg : tflgs) {
                    if (!flg || !flg->isTainted() || !flg->tag) {
                        continue;
                    }
                    TaintTag *tag = flg->tag;
                    if (flg->is_inherent) {
                        //This means current obj "o" is a taint source itself, and it has not been tainted by others (i.e. intact),
                        //so if it's a user taint source, we have already found a taint path, otherwise, there is no need to process
                        //this taint flag since its tag simply represents itself. 
                        if (!tag->is_global) {
                            //Construct the user taint path.
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                            dbgs() << "getAllUserTaintPaths(): current obj is a user taint source!\n";
#endif
                            insertTaintPath(history,res);
                            ++cnt_sp;
                        }
                        continue;
                    }
                    AliasObject *no = (AliasObject*)(tag->priv);
                    //If the TF is originated from a user taint source, we've found a path.
                    if (!tag->is_global) {
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                        dbgs() << "getAllUserTaintPaths(): got a user taint: ";
                        tag->dumpInfo_light(dbgs(),true);
#endif
                        std::set<void*> fs;
                        fs.insert((void*)flg);
                        TypeField ntf((no ? no->targetType : nullptr),tag->fieldId,no,&fs);
                        history.push_back(&ntf);
                        insertTaintPath(history,res);
                        history.pop_back();
                        ++cnt_sp;
                        continue;
                    }
                    //Ok, we now need to recursively explore the taint source of current TF, to avoid duplication,
                    //we group all such TFs by their taint source (e.g. obj|field in the tag).
                    if (no) {
                        wtfs[no][tag->fieldId].insert(flg);
                    }
                }
            }
            //Ok, now take care of the TFs that needs recursive processing.
            int r = 0;
            for (auto &e0 : wtfs) {
                AliasObject *no = e0.first;
                for (auto &e1 : e0.second) {
                    std::set<void*> tflgs;
                    for (auto t : e1.second) {
                        tflgs.insert(t);
                    }
                    TypeField ntf(no->targetType,e1.first,no,&tflgs);
                    r += getAllUserTaintPaths(&ntf,history,res);
                }
            }
            history.pop_back();
            if (!history.size()) {
                //In the end, don't forget to update the cache...
                pathMap[obj][fid] = res;
            }
            return r;
        }

        int getAllObjsForPath(std::vector<TypeField*> *p, std::set<AliasObject*> &res) {
            if (!p || !p->size()) {
                return 0;
            }
            std::set<AliasObject*> stageObjs, nextObjs;
            stageObjs.insert((AliasObject*)((*p)[0]->priv));
            int i = 0;
            for (;i < p->size() - 1; ++i) {
                TypeField *tf = (*p)[i];
                TypeField *ntf = (*p)[i+1];
                if (!tf || !ntf || !tf->priv || !ntf->priv) {
                   break;
                }
                if (stageObjs.empty()) {
                    break;
                }
                nextObjs.clear();
                //First decide the relationship between current typefield and the next one (e.g. point-to and embed)
                if (((AliasObject*)(ntf->priv))->parent == tf->priv) {
                    //Embed, we need to get all embedded objects at the same field of the objs in "stageObjs".
                    for (AliasObject *so : stageObjs) {
                        if (so && so->embObjs.find(tf->fid) != so->embObjs.end()) {
                            AliasObject *no = so->embObjs[tf->fid];
                            if (InstructionUtils::same_types(no->targetType,ntf->ty)) {
                                nextObjs.insert(no);
                            }
                        }
                    }
                }else {
                    //Point-to, need to find all pointee objects of the same field of the objs in "stageObjs".
                    for (AliasObject *so : stageObjs) {
                        if (!so || so->pointsTo.find(tf->fid) == so->pointsTo.end()) {
                            continue;
                        }
                        for (ObjectPointsTo *pto : so->pointsTo[tf->fid]) {
                            if (pto && pto->targetObject && (pto->dstfieldId == 0 || pto->dstfieldId == ntf->fid) && 
                                InstructionUtils::same_types(pto->targetObject->targetType,ntf->ty)) {
                                nextObjs.insert(pto->targetObject);
                            }
                        }
                    }
                }
                stageObjs.clear();
                stageObjs.insert(nextObjs.begin(),nextObjs.end());
            }
            //The leaf obj is always in the result set.
            TypeField *lastTf = (*p)[p->size()-1];
            if (lastTf && lastTf->priv) {
                res.insert((AliasObject*)(lastTf->priv));
            }
            //Add the inferred equivelant objects by path.
            if (i >= p->size() - 1) {
                res.insert(stageObjs.begin(),stageObjs.end());
            }
            return 0;
        }

        //Ret: 1 : eqv, 0 : not eqv, -1 : unknown
        int isEqvObj(AliasObject *o0, AliasObject *o1) {
            if (!o0 != !o1) {
                return 0;
            }
            if (!o0) {
                return 1;
            }
            for (std::set<AliasObject*> *cls : DRCHECKER::eqObjs) {
                if (!cls) {
                    continue;
                }
                if (cls->find(o0) != cls->end()) {
                    //Found the equivelant class in the cache...
                    return (cls->find(o1) != cls->end() ? 1 : 0);
                }
                if (cls->find(o1) != cls->end()) {
                    //Found the equivelant class in the cache...
                    return (cls->find(o0) != cls->end() ? 1 : 0);
                }
            }
            return -1;
        }

        //Due to our current multi-entry analysis logic, each entry function will be analyzed independently (e.g. it will not
        //re-use the AliasObject created by other entry functions, instead it will created its own copy), so here we need to
        //identify all potentially identical objects to the provided one, which ensures that our taint chain construction is
        //sound.
        int getAllEquivelantObjs(AliasObject *obj, std::set<AliasObject*> &res) {
            if (!obj) {
                return 0;
            }
            //Always includes itself.
            res.insert(obj);
            //Look up the cache.
            std::set<AliasObject*> *eqcls = nullptr;
            for (std::set<AliasObject*> *cls : DRCHECKER::eqObjs) {
                if (cls && cls->find(obj) != cls->end()) {
                    //Found the equivelant class in the cache...
                    eqcls = cls;
                    break;
                }
            }
            if (eqcls == nullptr) {
                //No equivelant class found in the cache, need to do the dirty work now...
                //By default the obj itself is in its own equivelant class.
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                dbgs() << "getAllEquivelantObjs(): identify eq objs for: " << (const void*)obj << "\n";
#endif
                eqcls = new std::set<AliasObject*>();
                eqcls->insert(obj);
                DRCHECKER::eqObjs.insert(eqcls);
                //First we need to collect all access paths to current object.
                //TODO: what if there is a pointsFrom obj who points to a non-zero field in "obj"?
                std::set<std::vector<TypeField*>*> *hty = getObjHierarchyTy(obj,0);
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                dbgs() << "getAllEquivelantObjs(): #accessPaths: " << (hty ? hty->size() : 0) << "\n";
#endif
                //Then based on each access path, we identify all the equivelant objects (i.e. those w/ the same access path).
                if (hty && hty->size()) {
                    for (std::vector<TypeField*> *ap : *hty) {
                        if (!ap || !ap->size()) {
                            continue;
                        }
                        getAllObjsForPath(ap,*eqcls);
                    }
                }
            }
            for (AliasObject *co : *eqcls) {
                //Objects bearing the same path may still have different types (e.g. those ->private pointers),
                //so it's necessary to make another type-based filtering here.
                if (!InstructionUtils::same_types(obj->targetType,co->targetType)) {
                    continue;
                }
                //If the target obj is a dummy one, then it can match any other object (dummy or not), 
                //otherwise, it can only match other dummy objects (i.e. two real objects cannot match).
                if (obj->auto_generated || co->auto_generated) {
                    res.insert(co);
                }
            }
            return 0;
        }

        //Given a taint flag (w/ a specific taint src A), we try to figure out whether there exists a taint path from an user input
        //U to A and then to the target instruction in the provided taint flag. Basically we try to return all direct or indirect
        //(e.g. go through multiple entry function invocations) taint paths from the user input to the target instruction affected
        //by the given taint flag.
        int getAllUserTaintChains(TaintFlag *tf, std::set<std::vector<InstLoc*>*> &res) {
            if (!tf || !tf->isTainted() || !tf->tag) {
                return 1;
            }
            TaintTag *tag = tf->tag;
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
            dbgs() << "getAllUserTaintChains(): enum user taint chains for tag: ";
            tag->dumpInfo_light(dbgs(),true);
#endif
            if (!tag->is_global) {
                //Ok this is already a user inited taint flag, return the trace in current TF immediately.
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                dbgs() << "getAllUserTaintChains(): this is already a user taint tag, return the TF trace directly!\n";
#endif
                std::vector<InstLoc*> *newPath = new std::vector<InstLoc*>();
                newPath->insert(newPath->end(),tf->instructionTrace.begin(),tf->instructionTrace.end());
                res.insert(newPath);
                return 0;
            }
            //Ok, so now what represented by "tag" is a global memory location, we need to inspect whether and how it can
            //be eventually tainted by the user input, and return the taint paths if any.
            if (tag->priv) {
                AliasObject *obj = (AliasObject*)tag->priv;
                std::vector<TypeField*> history;
                TypeField t(obj->targetType,tag->fieldId,(void*)obj);
                std::set<std::vector<InstLoc*>*> paths;
                getAllUserTaintPaths(&t,history,paths);
#ifdef DEBUG_CONSTRUCT_TAINT_CHAIN
                dbgs() << "getAllUserTaintChains(): Got " << paths.size() << " user taint paths in total.\n";
#endif
                //Append the taint trace in "tf".
                for (std::vector<InstLoc*> *ep : paths) {
                    //TODO: how to do the compatibility test?
                    if (!ep) {
                        continue;
                    }
                    std::vector<InstLoc*> *newPath = new std::vector<InstLoc*>(*ep);
                    newPath->insert(newPath->end(),tf->instructionTrace.begin(),tf->instructionTrace.end());
                    res.insert(newPath);
                }
            }
            return 0;
        }

        static bool in_hierarchy_history(AliasObject *obj, long field, std::vector<std::pair<long, AliasObject*>>& history, bool to_add) {
            /*
            auto to_check = std::make_pair(field, obj);
            if (std::find(history.begin(),history.end(),to_check) != history.end()) {
                return true;
            }
            */
            //We now ignore the field and only rely on obj id to detect the duplication.
            for (auto &e : history) {
                if (e.second == obj) {
                    return true;
                }
            }
            if (to_add) {
                auto to_check = std::make_pair(field, obj);
                history.push_back(to_check);
            }
            return false;
        }

        //NOTE: in this function we use quite some heuristics.
        static bool valid_history(std::vector<std::pair<long, AliasObject*>>& history) {
            if (history.size() < 8) {
                return true;
            }
            //Ok it's a long history, if it also contains some same typed object types, let's say it's invalid.
            std::set<Type*> tys;
            for (auto &e : history) {
                AliasObject *obj = e.second;
                if (!obj) {
                    return false;
                }
                if (tys.find(obj->targetType) != tys.end()) {
                    return false;
                }
                tys.insert(obj->targetType);
            }
            return true;
        }

        typedef int (*traverseHierarchyCallback)(std::vector<std::pair<long, AliasObject*>>& chain, bool recur);

        //Visit every object hierarchy chain ending w/ field "fid" of "obj", for each chain, invoke the passed-in callback
        //to enable some user-defined functionalities.
        static int traverseHierarchy(AliasObject *obj, long field, int layer, std::vector<std::pair<long, AliasObject*>>& history, 
                                     traverseHierarchyCallback cb = nullptr) {
#ifdef DEBUG_HIERARCHY
            dbgs() << layer << " traverseHierarchy(): " << (obj ? InstructionUtils::getTypeStr(obj->targetType) : "") 
            << " | " << field << " ID: " << (const void*)obj << "\n";
#endif
            if (!valid_history(history)) {
                //The history is too long or contains some duplicated elements (maybe due to the FP in static analysis),
                //so we decide to stop here...
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " traverseHierarchy(): Too long a history, unlikely to be real, stop..\n";
#endif
                if (cb) {
                    (*cb)(history,false);
                }
                return 1;
            }
            if (!obj) {
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " traverseHierarchy(): null obj.\n";
#endif
                return 0;
            }
            //TODO: is it really ok to exclude the local objects?
            if (obj->isFunctionLocal()) {
                //We're not interested in function local variables as they are not persistent.
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " traverseHierarchy(): function local objs.\n";
#endif
                return 0;
            }
            if (in_hierarchy_history(obj,field,history,true)) {
                //Exists in the history obj chain, should be a loop..
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " traverseHierarchy(): Exists in the obj chain..\n";
#endif
                auto curr = std::make_pair(field, obj);
                history.push_back(curr);
                if (cb) {
                    (*cb)(history,true);
                }
                history.pop_back();
                return 1;
            }
            int r = 0;
            if (obj->parent && obj->parent->embObjs.find(obj->parent_field) != obj->parent->embObjs.end() 
                && obj->parent->embObjs[obj->parent_field] == obj) {
                //Current obj is embedded in another obj.
#ifdef DEBUG_HIERARCHY
                dbgs() << layer << " traverseHierarchy(): find a host obj that embeds this one..\n";
#endif
                r += traverseHierarchy(obj->parent,obj->parent_field,layer+1,history,cb);
            }
            if (!obj->pointsFrom.empty()) {
                //Current obj may be pointed to by a field in another obj.
                for (auto &x : obj->pointsFrom) {
                    AliasObject *srcObj = x.first;
                    if (!srcObj) {
                        continue;
                    }
                    for (ObjectPointsTo *y : x.second) {
                        if (!y || y->targetObject != obj || (y->dstfieldId != 0 && y->dstfieldId != field)) {
                            continue;
                        }
#ifdef DEBUG_HIERARCHY
                        dbgs() << layer << " traverseHierarchy(): find a host object that can point to this one...\n";
#endif
                        r += traverseHierarchy(srcObj,y->fieldId,layer+1,history,cb);
                    }
                }
            }
            if (!r) {
                //This means current object is the root of the hierarchy chain, we should invoke the callback for this chain.
                if (cb) {
                    (*cb)(history,false);
                }
                r = 1;
            }
            history.pop_back();
            return r; 
        }

        static int hierarchyStrCb(std::vector<std::pair<long, AliasObject*>>& chain, bool recur) {
            if (chain.empty()) {
                return 0;
            }
            std::string s("");
            if (recur) {
                s += "<->";
            }
            for (int i = chain.size() - 1; i >= 0; --i) {
                long fid = chain[i].first;
                AliasObject *obj = chain[i].second;
                if (obj) {
                    s += (InstructionUtils::getTypeStr(obj->targetType) + ":" + std::to_string(fid));
                    if (i > 0) {
                        //Decide the relationship between current obj and the next obj in the chain (e.g. embed or point-to).
                        if (chain[i-1].second && chain[i-1].second->parent == obj) {
                            s += ".";
                        }else {
                            s += "->";
                        }
                    }
                }
            }
            if (s.size()) {
                DRCHECKER::hstrs.insert(s);
            }
            return 0;
        }

        static int hierarchyTyCb(std::vector<std::pair<long, AliasObject*>>& chain, bool recur) {
            if (chain.empty()) {
                return 0;
            }
            //Skip the duplicated node if the chain has any.
            int i = (recur ? chain.size() - 1 : chain.size());
            std::vector<TypeField*> *tys = new std::vector<TypeField*>();
            while (--i >= 0) {
                long fid = chain[i].first;
                AliasObject *obj = chain[i].second;
                if (obj) {
                    TypeField *currTf = new TypeField(obj->targetType,fid,(void*)obj);
                    tys->push_back(currTf);
                }
            }
            DRCHECKER::htys.insert(tys);
        }

        //A wrapper of getHierarchyStr() w/ a cache.
        static std::set<std::string> *getObjHierarchyStr(AliasObject *obj, long fid) {
            static std::map<AliasObject*,std::map<long,std::set<std::string>*>> cache;
            if (!obj) {
                return nullptr;
            }
            if (cache.find(obj) == cache.end() || cache[obj].find(fid) == cache[obj].end()) {
                std::vector<std::pair<long, AliasObject*>> history;
                history.clear();
                DRCHECKER::hstrs.clear();
                traverseHierarchy(obj, fid, 0, history, hierarchyStrCb);
                cache[obj][fid] = new std::set<std::string>(DRCHECKER::hstrs);
            }
            return cache[obj][fid];
        }

        //A wrapper of getHierarchyTy() w/ a cache.
        static std::set<std::vector<TypeField*>*> *getObjHierarchyTy(AliasObject *obj, long fid) {
            static std::map<AliasObject*,std::map<long,std::set<std::vector<TypeField*>*>*>> cache;
            if (!obj) {
                return nullptr;
            }
            if (cache.find(obj) == cache.end() || cache[obj].find(fid) == cache[obj].end()) {
                std::vector<std::pair<long, AliasObject*>> history;
                history.clear();
                for (auto &x : DRCHECKER::htys) {
                    delete(x);
                }
                DRCHECKER::htys.clear();
                traverseHierarchy(obj, fid, 0, history, hierarchyTyCb);
                cache[obj][fid] = new std::set<std::vector<TypeField*>*>();
                for (auto &x : DRCHECKER::htys) {
                    std::vector<TypeField*> *vtf = new std::vector<TypeField*>(*x);
                    cache[obj][fid]->insert(vtf);
                }
            }
            return cache[obj][fid];
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
                if (ty1) {
                    for (int i = 0; i < ty1->size() - 1; ++i) {
                        TypeField *tf1 = (*ty1)[i];
                        if (tf1 && tf0->is_same_ty(tf1)) {
                            return true;
                        }
                    }
                }
            }
            return false;
        }

        //Simply see whether "ty" matches any node in hty.
        bool in_hierarchy_ty(Type *ty, std::set<std::vector<TypeField*>*> *hty) {
            if (!ty || !hty) {
                return false;
            }
            for (auto &tv : *hty) {
                if (tv) {
                    for (TypeField *tf : *tv) {
                        if (tf && InstructionUtils::same_types(ty,tf->ty)) {
                            return true;
                        }
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
                if (!tag) {
                    continue;
                }
                std::set<std::vector<TypeField*>*> *hty0 = getObjHierarchyTy((AliasObject*)(tag->priv),tag->fieldId);
                if (!hty0) {
                    continue;
                }
                Type *ty0 = tag->getFieldTy();
                if (ty0 && ty0->isPointerTy()) {
                    ty0 = ty0->getPointerElementType();
                }
                //See whether its hierarchy is any other tag's prefix.
                bool is_prefix = false;
                for (TaintTag *t : *tags) {
                    if (!t || t == tag) {
                        //Exclude itself.
                        continue;
                    }
                    std::set<std::vector<TypeField*>*> *hty1 = getObjHierarchyTy((AliasObject*)(t->priv),t->fieldId);
                    if (!hty1) {
                        continue;
                    }
                    //whether it's a prefix in the type hierarchy.
                    if (is_prefix_hierarchy_ty(hty0,hty1)) {
                        is_prefix = true;
                        break;
                    }
                    //A complementary filtering to the above, see whether the final resulting type 
                    //of tag 0 matches any node in tag 1's type hierarchy.
                    if (ty0 && dyn_cast<CompositeType>(ty0) && in_hierarchy_ty(ty0,hty1)) {
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
                            std::set<std::string> *strs = getObjHierarchyStr((AliasObject*)(p->tag->priv),p->tag->fieldId);
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
                    std::set<std::string> *hstr = getObjHierarchyStr((AliasObject*)(tag->priv),tag->fieldId);
                    if (hstr && !hstr->empty()) {
                        int hc = 0;
                        for (auto& hs : *hstr) {
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
            
            //For debug use.
            ////////////////
            dbgs() << "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n";
            currWarning->printWarning(dbgs());
            dbgs() << "@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n";
            ////////////////

            this->addVulnerabilityWarningByInstr(currWarning);

        }
    };
}

#endif //PROJECT_MODULESTATE_H
