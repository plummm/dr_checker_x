//
// Created by machiry on 12/27/16.
//

#include "TaintUtils.h"

using namespace llvm;

#define DEBUG_ADD_NEW_TAINT_FLAG

namespace DRCHECKER {
    std::set<TaintFlag*>* TaintUtils::getTaintInfo(GlobalState &currState,
                                                   std::vector<Instruction *> *currFuncCallSites,
                                                   Value *targetVal) {
        // get total taint information for the context.
        std::map<Value *, std::set<TaintFlag*>*> *contextTaintInfo = currState.getTaintInfo(currFuncCallSites);
        // check if taint flags exits for the provided value?
        // if yes fetch it.
        if(contextTaintInfo->find(targetVal) != contextTaintInfo->end()) {
            return (*contextTaintInfo)[targetVal];
        }
        // else return null
        return nullptr;
    }

    void TaintUtils::updateTaintInfo(GlobalState &currState,
                                     std::vector<Instruction *> *currFuncCallSites,
                                     Value *targetVal,
                                     std::set<TaintFlag*> *targetTaintInfo) {

#ifdef DEBUG_ADD_NEW_TAINT_FLAG
        dbgs() << "TaintUtils::updateTaintInfo() for: " << InstructionUtils::getValueStr(targetVal) << "\n";
#endif
        std::set<TaintFlag*> *existingTaintInfo = TaintUtils::getTaintInfo(currState, currFuncCallSites, targetVal);
        // if there exists no previous taint info.
        if(existingTaintInfo == nullptr) {
            // get total taint information for the context.
            std::map<Value *, std::set<TaintFlag*>*> *contextTaintInfo = currState.getTaintInfo(currFuncCallSites);
            (*contextTaintInfo)[targetVal] = targetTaintInfo;
#ifdef DEBUG_ADD_NEW_TAINT_FLAG
            dbgs() << "No existing taint info, insert all...\n";
            if (targetTaintInfo) {
                for (TaintFlag *tf : *targetTaintInfo) {
                    if (tf && tf->tag) {
                        dbgs() << "++++TAG:\n";
                        tf->tag->dumpInfo(dbgs());
                    }
                }
            }
#endif
            return;
        }

        // ok there exists previous taint info.
        // check that for every taint flag if it is
        // already present? if yes, do not insert else insert
        for(auto currTaintFlag : *targetTaintInfo) {
            if (TaintUtils::addNewTaintFlag(existingTaintInfo, currTaintFlag)) {
#ifdef DEBUG_ADD_NEW_TAINT_FLAG
                if (currTaintFlag && currTaintFlag->tag) {
                    dbgs() << "++++TAG:\n";
                    currTaintFlag->tag->dumpInfo(dbgs());
                }
#endif
            }
        }
        // free the vector
        delete(targetTaintInfo);

    }

    int TaintUtils::addNewTaintFlag(std::set<TaintFlag*> *newTaintInfo, TaintFlag *newTaintFlag) {
        // check if the set already contains same taint?
        if(std::find_if(newTaintInfo->begin(), newTaintInfo->end(), [newTaintFlag](const TaintFlag *n) {
            return  n->isTaintEquals(newTaintFlag);
        }) == newTaintInfo->end()) {
            // if not insert the new taint flag into the newTaintInfo.
#ifdef DEBUG_ADD_NEW_TAINT_FLAG
            /*
            if (newTaintFlag->tag) {
                dbgs() << "TaintUtils::addNewTaintFlag: Add taint:\n";
                newTaintFlag->tag->dumpInfo(dbgs());
            }
            */
#endif
            newTaintInfo->insert(newTaintInfo->end(), newTaintFlag);
            return 1;
        } else {
            delete(newTaintFlag);
        }
        return 0;
    }
}
