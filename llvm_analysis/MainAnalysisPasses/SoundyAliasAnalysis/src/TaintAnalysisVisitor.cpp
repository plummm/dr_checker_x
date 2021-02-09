//
// Created by machiry on 12/5/16.
//

#include "TaintAnalysisVisitor.h"
#include "PointsToUtils.h"
#include "TaintUtils.h"
#include "getPath.h"
// #include "Universal.h"

using namespace llvm;
namespace DRCHECKER {

//#define DEBUG_CALL_INSTR
//#define DEBUG_RET_INSTR
//#define DEBUG_LOAD_INSTR
//#define DEBUG_CAST_INSTR
//#define DEBUG
//#define DEBUG_BIN_INSTR
#define ENFORCE_TAINT_PATH
//#define DEBUG_ENFORCE_TAINT_PATH
// #define DEBUG_STORE_INSTR_MAPPING

    

    InstLoc *TaintAnalysisVisitor::makeInstLoc(Value *v) {
        return new InstLoc(v,this->currFuncCallSites);
    }

    std::set<TaintFlag*>* TaintAnalysisVisitor::getTaintInfo(Value *targetVal) {
        return TaintUtils::getTaintInfo(this->currState, this->currFuncCallSites, targetVal);
    }

    void TaintAnalysisVisitor::debugInstTaint(Instruction &I){
        errs() << "\ndebugging inst: " << "\n";
        I.print(errs());
        errs() << "\n";
        auto inst = dyn_cast<CastInst>(&I);
        auto srcopr = inst->getOperand(0);
        auto taintmap = this->currState.taintInformation[this->currState.getContext(this->currFuncCallSites)];
        if(taintmap->find(srcopr) != taintmap->end()){
            errs() << "Found srcopr!\nsrcopr is: ";
            srcopr->print(errs());
            errs() << "\n";
            for(auto taintinfo : *(*taintmap)[srcopr]){
                if(taintinfo->isTainted()){
                    errs() << "srcopr is tainted!\n";
                }
            }
        }
        auto srcptos = this->getPtos(srcopr);
        if(srcptos){
            errs() << "srcopr has ptos!\n";
            errs() << "the size is: " << srcptos->size() << "\n";
            for(auto pto : *srcptos){
                if(pto->targetObject->targetType->isStructTy()){
                    errs() << "pto type is: " << pto->targetObject->targetType->getStructName().str() << "\n";
                }
                for(auto fdtts : pto->targetObject->taintedFields){
                    errs() << "fid: " << fdtts->fieldId << "\n";
                    for(auto fdtt : fdtts->targetTaint){
                        if(fdtt->isTainted()){
                            errs() << "tainted\n";
                        }else{
                            errs() << "not tainted\n";
                        }
                    }
                }
            }
        }
        if(taintmap->find(&I) != taintmap->end()){
            errs() << "Found dstopr!\ndstopr is: ";
            I.print(errs());
            errs() << "\n";
            for(auto taintinfo : *(*taintmap)[&I]){
                if(taintinfo->isTainted()){
                    errs() << "dstopr is tainted!\n";
                }
            }
        }
        auto dstptos = this->getPtos(&I);
        if(dstptos){
            errs() << "dstopr has ptos!\n";
            errs() << "the size is: " << dstptos->size() << "\n";
            for(auto pto : *dstptos){
                if(pto->targetObject->targetType->isStructTy()){
                    errs() << "pto type is: " << pto->targetObject->targetType->getStructName().str() << "\n";
                }
                for(auto fdtts : pto->targetObject->taintedFields){
                    errs() << "fid: " << fdtts->fieldId << "\n";
                    for(auto fdtt : fdtts->targetTaint){
                        if(fdtt->isTainted()){
                            errs() << "tainted\n";
                        }else{
                            errs() << "not tainted\n";
                        }
                    }
                }
            }
        }
        errs() << "\n";

        
        

    }

    bool reverseSeekBasicBlock(BasicBlock *startBB, BasicBlock *endBB, int depth) {
        for (auto it = pred_begin(startBB), et = pred_end(startBB); it != et; it++) {
            BasicBlock *pred = *it;
            if (pred == endBB)
                return true;
            if (depth>20)
                return false;
            return reverseSeekBasicBlock(pred, endBB, depth + 1);
        }
        return false;
    }

    void selectBranch(Instruction *lastins, BasicBlock *nextbb, string lastfilename, int lastline, std::ofstream &fout) {
        string brStr = "";

        int n = lastins->getNumOperands();
        if (n != 3) 
            return;
        BasicBlock *correctBB = dyn_cast<BasicBlock>(nextbb);
        BasicBlock *wrongBB;
        Value *br1 = lastins->getOperand(1);
        Value *br2 = lastins->getOperand(2);
        //errs() << "branches: " << br1 << " " << br2 << " " << (*nextbb) << "\n";
        if (br1 == nextbb)
            wrongBB = dyn_cast<BasicBlock>(br2);
        else
            wrongBB = dyn_cast<BasicBlock>(br1);

        if (correctBB->getUniquePredecessor() == nullptr)
            if (reverseSeekBasicBlock(correctBB, wrongBB, 1))
                brStr += "* ";  // Both branches are fesible

        if(lastfilename != "" && lastline != 0){
            brStr += lastfilename + ":" + to_string(lastline) + " ";
        }
        auto firstins = nextbb->getFirstNonPHIOrDbg();
        DebugLoc dbgloc;
        if (firstins != nullptr) {
            do {
                dbgloc = firstins->getDebugLoc();
                firstins = firstins->getNextNonDebugInstruction();
            } while((!dbgloc.get() || !dbgloc->getLine()) && firstins != nullptr);
        }

        if (dbgloc)
            brStr += dbgloc->getFilename().str() + ":" + to_string(dbgloc->getLine()) + " ";
        else
            return;

        firstins = wrongBB->getFirstNonPHIOrDbg();
        if (firstins != nullptr) {
            do {
                dbgloc = firstins->getDebugLoc();
                firstins = firstins->getNextNonDebugInstruction();
            } while((!dbgloc || (dbgloc->getLine() == 0)) && firstins != nullptr);
        }
        if (dbgloc)
            brStr += dbgloc->getFilename().str() + ":" + to_string(dbgloc->getLine()) + "\n";
        else
            return;
        //errs() << brStr;
        fout << brStr;
    }

    void printPath(std::vector<Instruction*> *CallSites, Instruction *site, int skipfirstbb, int filecount, std::string filenameprefix = ""){
        std::vector<llvm::BasicBlock *> thePath;
        int skip = 0;
        for(auto i = 0; i < CallSites->size() - 1; i += 2){
            getPath* pathfinder = new getPath();
            auto src = (*CallSites)[i]->getParent();
            auto dst = (*CallSites)[i + 1]->getParent();
            pathfinder->BBvisitor(src, dst, 0);
            pathfinder->DFSvisit(src, dst);
            if(pathfinder->ShortestPath){
                auto skiped = false;
                for(auto bb : *(pathfinder->ShortestPath)){
                    if(0 < skip && skip < skipfirstbb && !skiped){
                        skip++;
                        skiped = true;
                    }else{
                        thePath.push_back(bb);
                    }
                    if(skip == 0){
                        skip++;
                    }
                    
                }
            }
            delete pathfinder;
        }
        getPath* pathfinder = new getPath();
        auto src = (*CallSites)[CallSites->size() - 1]->getParent();
        auto dst = site->getParent();
        pathfinder->BBvisitor(src, dst, 0);
        pathfinder->DFSvisit(src, dst);
        if(pathfinder->ShortestPath){
            auto skiped = false;
            for(auto bb : *(pathfinder->ShortestPath)){
                if(0 < skip && skip < skipfirstbb && !skiped){
                    skip++;
                    skiped = true;
                }else{
                    thePath.push_back(bb);
                }
                if(skip == 0){
                    skip++;
                }
            }
        }
        
        delete pathfinder;
        // errs() << "\n\n";
        ofstream fout;
        int bb_num = thePath.size();
        fout.open(filenameprefix + to_string(bb_num) + "-" + to_string(filecount));
        for(auto bb = thePath.begin(), be = thePath.end(); bb != be; bb++){
            auto firstins = (*bb)->getFirstNonPHIOrDbg();
            if (firstins == nullptr)
                continue;
            auto nextbb = bb + 1;
            auto dbgloc = firstins->getDebugLoc();
            while((!dbgloc || (dbgloc->getLine() == 0)) && !firstins->isTerminator()){
                firstins = firstins->getNextNonDebugInstruction();
                if (firstins != nullptr)
                    dbgloc = firstins->getDebugLoc();
                else
                    dbgloc = nullptr;
            }
            std::string firstfilename = "";
            unsigned int firstline = 0;
            if(dbgloc){
                firstfilename = dbgloc->getFilename().str();
                firstline = dbgloc->getLine();
            } else
                continue;
            dbgloc = nullptr;
            auto lastins = (*bb)->getTerminator();
            if (lastins == nullptr)
                continue;
            while((!dbgloc || (dbgloc->getLine() == 0)) && firstins != (*bb)->getFirstNonPHIOrDbg()){
                lastins = lastins->getPrevNonDebugInstruction();
                if (lastins != nullptr)
                    dbgloc = lastins->getDebugLoc();
                else
                    break;
            }
            std::string lastfilename = "";
            unsigned int lastline = 0;
            if(dbgloc){
                lastfilename = dbgloc->getFilename().str();
                lastline = dbgloc->getLine();
            } else
                continue;

            if (isa<BranchInst>(lastins)) {
                if (nextbb != be && (*bb)->getParent() == (*nextbb)->getParent()) {
                    selectBranch(lastins, *nextbb, lastfilename, lastline, fout);
                } else {
                    errs() << lastfilename << ":" << lastline << "\n";
                }
            }
        }
        
        fout << site->getDebugLoc()->getFilename().str() << ":" << to_string(site->getDebugLoc()->getLine()) << "\n";
        fout << "$\n";
        string str;
        llvm::raw_string_ostream(str) << *site;
        fout << str << "\n";
        fout.close();
    }

    void fromVultoUse(std::vector<Instruction *> *vulcallsites, std::vector<Instruction *> *usecallsites, Instruction *usesite, int filecount, std::string filenameprefix = ""){
        std::vector<Instruction *> cpvulcallsites, cpusecallsites;
        std::vector<Instruction *> *PathfromVultoUse = new std::vector<Instruction *>();
        auto smallsize = vulcallsites->size() > usecallsites->size() ? usecallsites->size() : vulcallsites->size();
        int i = 0;
        for(; i < smallsize; i++){
            if((*vulcallsites)[i] != (*usecallsites)[i]){
                break;
            }
        }
        int tmp = i;
        for(; tmp < vulcallsites->size(); tmp++){
            cpvulcallsites.push_back((*vulcallsites)[tmp]);
        }
        tmp = i;
        for(; tmp < usecallsites->size(); tmp++){
            cpusecallsites.push_back((*usecallsites)[tmp]);
        }
        for(auto idx = cpvulcallsites.size() - 1; idx > 0; idx -= 2){
            PathfromVultoUse->push_back(cpvulcallsites[idx]);
            auto getret = new getRet();
            getret->BBvisit(cpvulcallsites[idx]->getParent(), 0);
            if(getret->found){
                PathfromVultoUse->push_back(getret->ret);
            }else{
                errs() << "unable to find a ret inst!\n";
                return;
            }
            
        }
        PathfromVultoUse->push_back(cpvulcallsites[0]);
        for(auto idx = 1; idx < cpusecallsites.size(); idx += 2){
            PathfromVultoUse->push_back(cpusecallsites[idx - 1]);
            PathfromVultoUse->push_back(cpusecallsites[idx]);
        }
        printPath(PathfromVultoUse, usesite, (cpvulcallsites.size() + 1) / 2, filecount, filenameprefix);

    }

    //"I" is the inst site where need the ptr taint info. 
    void TaintAnalysisVisitor::getPtrTaintInfo(Value *targetVal, std::set<TaintFlag*> &retTaintFlag, Instruction *I) {
        std::set<PointerPointsTo*> *currPtsTo = PointsToUtils::getPointsToObjects(this->currState, this->currFuncCallSites, targetVal);
        if(currPtsTo == nullptr) {
            return;
        }
        InstLoc *loc = this->makeInstLoc(I);
        for (PointerPointsTo *currPtTo : *currPtsTo) {
            std::set<TaintFlag*> currTaintSet;
            currPtTo->targetObject->getFieldTaintInfo(currPtTo->dstfieldId,currTaintSet,loc);
            if (currTaintSet.size()) {
                for(auto a : currTaintSet) {
                    if(std::find_if(retTaintFlag.begin(), retTaintFlag.end(), [a](const TaintFlag *n) {
                        return  n->isTaintEquals(a);
                    }) == retTaintFlag.end()) {
                        // if not insert the new taint flag into the newTaintInfo.
                        retTaintFlag.insert(a);
                    }
                }
            }
        }
    }

    void TaintAnalysisVisitor::updateTaintInfo(Value *targetVal, std::set<TaintFlag*> *targetTaintInfo) {
        TaintUtils::updateTaintInfo(this->currState, this->currFuncCallSites, targetVal, targetTaintInfo);
    }

    std::set<TaintFlag*> *TaintAnalysisVisitor::makeTaintInfoCopy(Instruction *targetInstruction, std::set<TaintFlag*> *srcTaintInfo, 
                                                                  std::set<TaintFlag*> *dstTaintInfo) {
        if (srcTaintInfo != nullptr) {
            std::set<TaintFlag*> *newTaintInfo = new std::set<TaintFlag*>();
            InstLoc *loc = this->makeInstLoc(targetInstruction);
            bool add_taint = false;
            for (auto currTaint : *srcTaintInfo) {
                if (!currTaint) {
                    continue;
                }
                add_taint = true;
                //hz: we're doing the taint analysis for global states, which can survive function invocations,
                //stmt0 in the 1st function call may affect stmt1 in the 2nd invocation of the same function,
                //although stmt0 cannot reach stmt1 in the CFG of this function, so it seems we should disable the below reachability check.
                //However, we can rely on the post-processing to do the multi-entry fixed-point analysis, and here we still
                //enforce the reachability test to avoid the taint explosion and have a better and cleaner summary of a single entry function.
#ifdef ENFORCE_TAINT_PATH
                if (currTaint->targetInstr != nullptr && !currTaint->is_inherent) {
                    if (targetInstruction) {
                        add_taint = loc->reachable(currTaint->targetInstr);
                    }
                }
#endif
                if (add_taint) {
                    TaintFlag *newTaintFlag = new TaintFlag(currTaint, loc);
                    TaintAnalysisVisitor::addNewTaintFlag(newTaintInfo,newTaintFlag);
                }else {
#ifdef DEBUG_ENFORCE_TAINT_PATH
                    dbgs() << "TaintAnalysisVisitor::makeTaintInfoCopy(): Failed to pass the taint path test, the TaintFlag:\n";
                    currTaint->dumpInfo(dbgs());
                    dbgs() << "Src Inst: ";
                    if (currTaint->targetInstr) {
                        currTaint->targetInstr->print(dbgs());
                    }else {
                        dbgs() << "\n";
                    }
                    dbgs() << "Dst Inst: ";
                    loc->print(dbgs());
#endif
                }
            }
            // if no taint info is propagated.
            if (newTaintInfo->empty()) {
                delete(newTaintInfo);
                delete(loc);
                newTaintInfo = nullptr;
            }
            // if dstTaintInfo is not null.
            if (dstTaintInfo != nullptr && newTaintInfo != nullptr) {
                // copy all the taint info into dstTaintInfo.
                if (dstTaintInfo->empty()) {
                    //No need to check for duplication of existing elements in "dstTaintInfo".
                    dstTaintInfo->insert(newTaintInfo->begin(), newTaintInfo->end());
                }else {
                    for (TaintFlag *tf : *newTaintInfo) {
                        TaintAnalysisVisitor::addNewTaintFlag(dstTaintInfo,tf);
                    }
                }
                // delete new taint info
                delete(newTaintInfo);
                // set return value of dstTaintInfo
                newTaintInfo = dstTaintInfo;
            }
            return newTaintInfo;
        }
        return nullptr;
    }

    std::set<TaintFlag*>* TaintAnalysisVisitor::makeTaintInfoCopy(Instruction *targetInstruction, TaintFlag *srcTaintFlag, 
                                                                  std::set<TaintFlag*> *dstTaintInfo) {
        if (!srcTaintFlag) {
            return nullptr;
        }
        std::set<TaintFlag*> srcTaintInfo;
        srcTaintInfo.insert(srcTaintFlag);
        return TaintAnalysisVisitor::makeTaintInfoCopy(targetInstruction,&srcTaintInfo,dstTaintInfo);
    }

    //Get the taint flags of the specified value, strip the cast when necessary.
    std::set<TaintFlag*> *TaintAnalysisVisitor::getTFs(Value *v) {
        if (!v) {
            return nullptr;
        }
        std::set<TaintFlag*> *tfs = this->getTaintInfo(v);
        if (tfs && !tfs->empty()) {
            return tfs;
        }
        //E.g. "v" might be: (1) GEP (cast..) ... (2) cast (GEP ...) ..., in such cases we need to retrieve the taint
        //from the innermost base pointer.
        //Try stripping the simple cast if any.
        Value *v0 = v->stripPointerCasts();
        //Further strip the GEP transformation.
        //TODO: not sure whether this is the best choice to strip the GEP transformation, at least one obvious weakness
        //is it can only strip the GEP w/ all constant indicies.
        Value *v1 = v->stripInBoundsConstantOffsets();
        //First try the more closer "v0".
        if (v0 && v0 != v) {
            tfs = this->getTaintInfo(v0);
            if (tfs && !tfs->empty()) {
                return tfs;
            }
        }
        //Then "v1".
        if (v1 && v1 != v && v1 != v0) {
            tfs = this->getTaintInfo(v1);
            if (tfs && !tfs->empty()) {
                return tfs;
            }
        }
        //GG
        return tfs;
    }

    //This function will try best to get the pto info of a pointer value, if the raw pointer doesn't have pto, 
    //it will do the necessary cast strip.
    //NOTE: this is a helper function designed for the taint analysis, which also needs to obtain the pto info in some cases,
    //but different from the same named function in alias analysis, we don't need to parse the embedded GEP since its pto
    //info has already been set up by the alias analysis, neither the dummy object creation.
    std::set<PointerPointsTo*> *TaintAnalysisVisitor::getPtos(Value *srcPointer) { 
        if (!srcPointer) {
            return nullptr;
        }
        if (PointsToUtils::hasPointsToObjects(this->currState, this->currFuncCallSites, srcPointer)) {
            return PointsToUtils::getPointsToObjects(this->currState, this->currFuncCallSites, srcPointer); 
        }
        //Try to strip the pointer cast.
        Value *v = srcPointer->stripPointerCasts();
        if (v && v != srcPointer) {
            return PointsToUtils::getPointsToObjects(this->currState, this->currFuncCallSites, v); 
        }
        return nullptr;
    }

    std::set<TaintFlag*> *TaintAnalysisVisitor::mergeTaintInfo(std::set<Value*> &srcVals, Instruction *targetInstr) {

        std::set<TaintFlag*> *newTaintInfo = new std::set<TaintFlag*>();
        for(auto currVal : srcVals) {
            std::set<TaintFlag*> *currValTaintInfo = this->getTFs(currVal);
            if(currValTaintInfo && !currValTaintInfo->empty()) {
                this->makeTaintInfoCopy(targetInstr, currValTaintInfo, newTaintInfo);
            }
        }
        // if there is no taint info?
        if(newTaintInfo->empty()) {
            // delete the object.
            delete(newTaintInfo);
            newTaintInfo = nullptr;
        }
        return newTaintInfo;
    }

    int TaintAnalysisVisitor::addNewTaintFlag(std::set<TaintFlag*> *newTaintInfo, TaintFlag *newTaintFlag) {
        return TaintUtils::addNewTaintFlag(newTaintInfo, newTaintFlag);
    }

    void TaintAnalysisVisitor::visitAllocaInst(AllocaInst &I) {
        // Nothing to do for TaintAnalysis
    }

    void TaintAnalysisVisitor::visitCastInst(CastInst &I) {
        // handles cast instruction.

        // if the src operand is tainted then the instruction is tainted.

        Value *srcOperand = I.getOperand(0);
        std::set<TaintFlag*> *srcTaintInfo = this->getTFs(srcOperand);

        // if there exists some taintflags..propagate them
        if (srcTaintInfo && !srcTaintInfo->empty()) {
            std::set<TaintFlag*> *newTaintInfo = this->makeTaintInfoCopy(&I, srcTaintInfo);
            if (newTaintInfo && !newTaintInfo->empty()) {
                this->updateTaintInfo(&I, newTaintInfo);
            }else {
#ifdef DEBUG_CAST_INSTR
                dbgs() << "Taint Info cannot be propagated because the current instruction is not reachable from"
                << "  tainted source at " << InstructionUtils::getValueStr(&I) << "\n";
#endif
            }
        }

        auto taintmap = this->currState.taintInformation[this->currState.getContext(this->currFuncCallSites)];
        if(taintmap->find(srcOperand) != taintmap->end()){
            for(auto taintinfo : *(*taintmap)[srcOperand]){
                if(taintinfo->isTainted()){
                    auto dstptos = this->getPtos(&I);
                    if(dstptos){
                        bool hastainted = false;
                        for(auto pto : *dstptos){
                            if(pto->targetObject->taintedFields.size() > 0){
                                hastainted = true;
                            }
                        }
                        if(!hastainted){
                            for(auto pto : *dstptos){
                                auto instloc = new InstLoc(&I, this->currFuncCallSites);
                                pto->targetObject->setAsTaintFieldSrc(instloc, this->currState.getDataLayout(), true, 0);
                            }
                        }
                    }
                    break;
                }
            }
        }

        // auto currtoptaintinfo = this->currState.taintInformation[this->currState.getContext(this->currFuncCallSites)];
        // if(currtoptaintinfo){
        //     errs() << "found currtoptaintinfo\n" << "\n";
        //     if(currtoptaintinfo->find(srcOperand) != currtoptaintinfo->end()){
        //         errs() << "found srcopr taint info\n";
        //         for(auto ttinfo : *(*currtoptaintinfo)[srcOperand]){
        //             if(ttinfo->isTainted()){
        //                 errs() << "tainted!\n" << "\n";
        //             }
        //         }
        //     }
        // }
        

        //debugInstTaint(I);

        // auto ptos = this->getPtos(&I);
        // if(ptos){
        //         for(auto pto : *ptos){
        //         if(pto->targetObject->embObjs.size() > 0){
        //             errs() << "embedded!" << "\n";
        //         }
        //     }
        // }
        
    }

    void TaintAnalysisVisitor::visitBinaryOperator(BinaryOperator &I) {
        // merge taint flag of all the operands.
        std::set<Value*> allVals;
        allVals.insert(allVals.end(), I.getOperand(0));
        allVals.insert(allVals.end(), I.getOperand(1));
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
#ifdef DEBUG_BIN_INSTR
            dbgs() << "Propagating taint in binary instruction\n";
#endif
            updateTaintInfo(&I, newTaintInfo);
        }

    }

    void TaintAnalysisVisitor::visitPHINode(PHINode &I) {
        // get all values that need to be merged.
        std::set<Value*> allVals;
        for(unsigned i=0;i<I.getNumIncomingValues(); i++) {
            allVals.insert(allVals.end(), I.getIncomingValue(i));
        }
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }
    }

    void TaintAnalysisVisitor::visitSelectInst(SelectInst &I) {
        /***
         *  Merge taintinfo of all the objects
         *  reaching this select instruction.
         */
        // get all values that need to be merged.
        std::set<Value*> allVals;
        allVals.insert(allVals.end(), I.getTrueValue());
        allVals.insert(allVals.end(), I.getFalseValue());

        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }

    }

    void TaintAnalysisVisitor::visitGetElementPtrInst(GetElementPtrInst &I) {
        // the GEP instruction always computes pointer, which is used to

        // check if one of the operand is tainted?
        // get all values that need to be merged.
        std::set<Value*> allVals;
        for(unsigned i=0; i<I.getNumOperands(); i++) {
            Value* currOp = I.getOperand(i);
            // RangeAnalysis::Range currRange = this->currState.getRange(currOp);
            // if(currRange.isBounded()) {
            //     // if the range of the index we use is bounded?
            //     // it may not be bad.
            //     continue;
            // }
            allVals.insert(allVals.end(), currOp);
        }
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }

        //debug for taint
        //errs() << "debugging gep inst\n";
        //I.print(errs());
        //errs() <<"\n";
        

    }

    void TaintAnalysisVisitor::visitLoadInst(LoadInst &I) {
#ifdef DEBUG_LOAD_INSTR
        dbgs() << "TaintAnalysisVisitor::visitLoadInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value *srcPointer = I.getPointerOperand();
        std::set<TaintFlag*> *srcTaintInfo = this->getTFs(srcPointer);
        std::set<TaintFlag*> *newTaintInfo = new std::set<TaintFlag*>();

        //Copy the taint from tainted pointer.
        if (srcTaintInfo && !srcTaintInfo->empty()) {
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "The src pointer itself is tainted.\n";
#endif
            TaintAnalysisVisitor::makeTaintInfoCopy(&I,srcTaintInfo,newTaintInfo);
        }
        //Now get the pto info of the src pointer.
        std::set<PointerPointsTo*> *srcPointsTo = this->getPtos(srcPointer);
        /*if (srcPointsTo == nullptr){
            errs() << "No ptos for src ptr ";
            // I.print(errs());
            errs() << "\n";
        }*/
        if (srcPointsTo && !srcPointsTo->empty()) {
            // this set stores the <fieldid, targetobject> of all the objects to which the srcPointer points to.
            std::set<std::pair<long, AliasObject *>> targetObjects;
            for (PointerPointsTo *currPointsToObj : *srcPointsTo) {
                long target_field = currPointsToObj->dstfieldId;
                AliasObject *dstObj = currPointsToObj->targetObject;
                auto fdtaintinfo = dstObj->getFieldTaint(target_field);
                
                if(fdtaintinfo){
                    for(auto taintinfo : fdtaintinfo->targetTaint){
                        if(taintinfo->isTainted()){
                            // errs() << "Load" << "\n";
                            // I.print(errs());
                            // errs() << "\n";
                            // errs() << I.getDebugLoc()->getFilename() << "\n";
                            // errs() << I.getDebugLoc()->getLine() << "\n";
                            for(auto user : I.users()){
                                if(isa<CallInst>(&*user)){
                                    auto nextcall = dyn_cast<CallInst>(&*user);
                                    if(nextcall->getCalledValue() == dyn_cast<Value>(&I)
                                     || nextcall->getCalledValue()->stripPointerCasts() == dyn_cast<Value>(&I)
                                     && this->currState.visitedsites.find(nextcall) == this->currState.visitedsites.end()){
#ifdef DEBUG_CALL_INSTR
                                        errs() << "Func call dereference" << "\n";
                                        nextcall->print(errs());
                                        errs() << "\n";
#endif
                                        errs() << nextcall->getDebugLoc()->getFilename() << "\n";
                                        errs() << nextcall->getDebugLoc()->getLine() << "\n";
                                        fromVultoUse(&this->currState.vulsitecontext, this->currFuncCallSites, nextcall, this->currState.filecounter++, this->currState.printPathDir + "/path2FuncPtrDef-");
                                        this->currState.visitedsites.insert(nextcall);
                                        this->currState.taintedindirectcalls.insert(nextcall);
                                    }
                                }
                            }
                        }
                    }
                }
                auto to_check = std::make_pair(target_field, dstObj);
                if (std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                    targetObjects.insert(targetObjects.end(), to_check);
                    //Ok, now fetch the taint flags from the object field..
                    std::set<TaintFlag*> fieldTaintInfo, nTaintInfo;
                    dstObj->getFieldTaintInfo(target_field,fieldTaintInfo,this->makeInstLoc(&I));
                    if (fieldTaintInfo.empty()) {
#ifdef DEBUG_LOAD_INSTR
                        dbgs() << "No taint information available for: " << (const void*)dstObj << "|" << target_field << "\n";
#endif
                        continue;
                    }
                    this->makeTaintInfoCopy(&I, &fieldTaintInfo, &nTaintInfo);
                    //Now set up the load tag for the new TFs and insert them into the final "newTaintInfo".
                    for (TaintFlag *tf : nTaintInfo) {
                        if (TaintAnalysisVisitor::addNewTaintFlag(newTaintInfo,tf)) {
                            //TF inserted, set up the load tag.
                            tf->loadTag = currPointsToObj->loadTag;
                        }
                    }
                }
            }
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "Got pointee objs of srcPointer, #: " << targetObjects.size() << "\n";
#endif
        } else {
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "TaintAnalysis: Src Pointer does not point to any object.\n";
#endif
        }
        if(newTaintInfo->size()) {
            // okay. Now add the newTaintInfo
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "TaintAnalysis: Updating Taint in LoadInstruction..\n";
#endif
            updateTaintInfo(&I, newTaintInfo);
        } else {
            delete(newTaintInfo);
        }

        //debugInstTaint(I);

    }

    void inferTaintMap(StoreInst &I, std::set<TaintFlag*> *srcTFs, std::set<PointerPointsTo*> *dstPtos, 
                       std::map<PointerPointsTo*,std::set<TaintFlag*>> &taintMap) {
        if (!srcTFs || !dstPtos) {
            return;
        }
#ifdef DEBUG_STORE_INSTR_MAPPING
        dbgs() << "inferTaintMap(): #srcTFs: " << srcTFs->size() << " #dstPtos: " << dstPtos->size() << "\n";
#endif
        if (srcTFs->empty() || dstPtos->size() <= 1) {
            return;
        }
        //Verify that the dst pointees share a unified loadTag.
        std::vector<TypeField*> *dtag = &((*(dstPtos->begin()))->loadTag);
        int dl = dtag->size(); 
        for (PointerPointsTo *pto : *dstPtos) {
            dl = std::min(dl,InstructionUtils::isSimilarLoadTag(dtag,&(pto->loadTag)));
            if (dl <= 0) {
#ifdef DEBUG_STORE_INSTR_MAPPING
                dbgs() << "inferTaintMap(): The load tags are not uniformed between dsts.\n";
#endif
                return;
            }
        }
        //Set up the mapping, note that here we skip the unification verification step for the src as in point-to analysis,
        //since unlike the pto records, the taint flags have multiple different sources (e.g. in a load IR they can be from both
        //the src pointer itself and the pointee mem locations..). So what we do here is more aggressive: to try best to match 
        //those TFs that can be addressed to a certain dst mem location, and only for the remaining, propagate them to all dsts.
        std::set<TaintFlag*> addedTFs;
        for (PointerPointsTo *pto : *dstPtos) {
            std::vector<TypeField*> *dt = &(pto->loadTag);
            taintMap[pto].clear();
            for (TaintFlag *tf : *srcTFs) {
                std::vector<TypeField*> *st = &(tf->loadTag);
                if (InstructionUtils::matchLoadTags(dt,st,dl,0) >= 0) {
                    taintMap[pto].insert(tf);
                    addedTFs.insert(tf);
                }else {
#ifdef DEBUG_STORE_INSTR_MAPPING
                    dbgs() << "inferTaintMap(): Skip the TF: ";
                    tf->dumpInfo_light(dbgs(),false);
                    dbgs() << " for " << pto->targetObject << "|" << pto->dstfieldId << "\n";
#endif
                }
            }
        }
        //TODO: What to do w/ the unmapped TFs..
        /*
        if (addedTFs.size() < srcTFs->size()) {
            for (TaintFlag *tf : *srcTFs) {
                if (addedTFs.find(tf) == addedTFs.end()) {
                }
            }
        }
        */
    }

    // Even though I dont want to touch any code in this function
    // But the branch selection strategy is so import
    // Let me do this
    void printPath2(std::vector<Instruction*> *Vul2Ass, std::vector<Instruction*> *Ass2Use, Instruction *asssite, Instruction *usesite, int skipfirstbb1, int skipfirstbb2, int filecount, std::string filenameprefix = ""){
        std::vector<llvm::BasicBlock *> thePath1;
        int skip = 0;
        for(auto i = 0; i < Vul2Ass->size() - 1; i += 2){
            getPath* pathfinder = new getPath();
            auto src = (*Vul2Ass)[i]->getParent();
            auto dst = (*Vul2Ass)[i + 1]->getParent();
            pathfinder->BBvisitor(src, dst, 0);
            pathfinder->DFSvisit(src, dst);
            if(pathfinder->ShortestPath){
                auto skiped = false;
                for(auto bb : *(pathfinder->ShortestPath)){
                    if(0 < skip && skip < skipfirstbb1 && !skiped){
                        skip++;
                        skiped = true;
                    }else{
                        thePath1.push_back(bb);
                    }
                    if(skip == 0){
                        skip++;
                    }
                    
                }
            }
            delete pathfinder;
        }
        getPath* pathfinder = new getPath();
        auto src = (*Vul2Ass)[Vul2Ass->size() - 1]->getParent();
        auto dst = asssite->getParent();
        pathfinder->BBvisitor(src, dst, 0);
        pathfinder->DFSvisit(src, dst);
        if(pathfinder->ShortestPath){
            auto skiped = false;
            for(auto bb : *(pathfinder->ShortestPath)){
                if(0 < skip && skip < skipfirstbb1 && !skiped){
                    skip++;
                    skiped = true;
                }else{
                    thePath1.push_back(bb);
                }
                if(skip == 0){
                    skip++;
                }
            }
        }
        
        delete pathfinder;
        ofstream fout;
        int bb_num = thePath1.size();
        fout.open(filenameprefix + to_string(bb_num) + "-" + to_string(filecount));
        for(auto bb = thePath1.begin(), be = thePath1.end(); bb != be; bb++){
            auto firstins = (*bb)->getFirstNonPHIOrDbg();
            auto nextbb = bb + 1;
            auto dbgloc = firstins->getDebugLoc();
            while((!dbgloc || (dbgloc->getLine() == 0)) && !firstins->isTerminator()){
                firstins = firstins->getNextNonDebugInstruction();
                dbgloc = firstins->getDebugLoc();
            }
            std::string firstfilename = "";
            unsigned int firstline = 0;
            if(dbgloc){
                firstfilename = dbgloc->getFilename().str();
                firstline = dbgloc->getLine();
            }
            auto lastins = (*bb)->getTerminator();
            dbgloc = lastins->getDebugLoc();
            while((!dbgloc || (dbgloc->getLine() == 0)) && firstins != (*bb)->getFirstNonPHIOrDbg()){
                lastins = lastins->getPrevNonDebugInstruction();
                if (lastins != nullptr)
                    dbgloc = lastins->getDebugLoc();
                else
                    break;
            }
            std::string lastfilename = "";
            unsigned int lastline = 0;
            if(dbgloc){
                lastfilename = dbgloc->getFilename().str();
                lastline = dbgloc->getLine();
            }
            if (isa<BranchInst>(lastins)) {
                if (nextbb != be && (*bb)->getParent() == (*nextbb)->getParent()) {
                    selectBranch(lastins, *nextbb, lastfilename, lastline, fout);
                } else {
                    errs() << lastfilename << ":" << lastline << "\n";
                }
            }
        }


        std::vector<llvm::BasicBlock *> thePath2;
        skip = 0;
        for(auto i = 0; i < Ass2Use->size() - 1; i += 2){
            getPath* pathfinder = new getPath();
            auto src = (*Ass2Use)[i]->getParent();
            auto dst = (*Ass2Use)[i + 1]->getParent();
            pathfinder->BBvisitor(src, dst, 0);
            pathfinder->DFSvisit(src, dst);
            if(pathfinder->ShortestPath){
                auto skiped = false;
                for(auto bb : *(pathfinder->ShortestPath)){
                    if(0 < skip && skip < skipfirstbb2 && !skiped){
                        skip++;
                        skiped = true;
                    }else{
                        thePath2.push_back(bb);
                    }
                    if(skip == 0){
                        skip++;
                    }
                    
                }
            }
            delete pathfinder;
        }
        getPath* pathfinder2 = new getPath();
        src = (*Ass2Use)[Ass2Use->size() - 1]->getParent();
        dst = usesite->getParent();
        pathfinder2->BBvisitor(src, dst, 0);
        pathfinder2->DFSvisit(src, dst);
        if(pathfinder2->ShortestPath){
            auto skiped = false;
            for(auto bb : *(pathfinder2->ShortestPath)){
                if(0 < skip && skip < skipfirstbb2 && !skiped){
                    skip++;
                    skiped = true;
                }else{
                    thePath2.push_back(bb);
                }
                if(skip == 0){
                    skip++;
                }
            }
        }
        
        delete pathfinder2;
        for(auto bb = thePath2.begin(), be = thePath2.end(); bb != be; bb++){
            auto firstins = (*bb)->getFirstNonPHIOrDbg();
            auto nextbb = bb + 1;
            auto dbgloc = firstins->getDebugLoc();
            while((!dbgloc || (dbgloc->getLine() == 0)) && !firstins->isTerminator()){
                firstins = firstins->getNextNonDebugInstruction();
                dbgloc = firstins->getDebugLoc();
            }
            std::string firstfilename = "";
            unsigned int firstline = 0;
            if(dbgloc){
                firstfilename = dbgloc->getFilename().str();
                firstline = dbgloc->getLine();
            }
            auto lastins = (*bb)->getTerminator();
            dbgloc = lastins->getDebugLoc();
            while((!dbgloc || (dbgloc->getLine() == 0)) && firstins != (*bb)->getFirstNonPHIOrDbg()){
                lastins = lastins->getPrevNonDebugInstruction();
                if (lastins != nullptr)
                    dbgloc = lastins->getDebugLoc();
                else
                    break;
            }
            std::string lastfilename = "";
            unsigned int lastline = 0;
            if(dbgloc){
                lastfilename = dbgloc->getFilename().str();
                lastline = dbgloc->getLine();
            }
            if (isa<BranchInst>(lastins)) {
                if (nextbb != be && (*bb)->getParent() == (*nextbb)->getParent()) {
                    selectBranch(lastins, *nextbb, lastfilename, lastline, fout);
                } else {
                    errs() << lastfilename << ":" << lastline << "\n";
                }
            }
        }

        fout << usesite->getDebugLoc()->getFilename().str() << ":" << to_string(usesite->getDebugLoc()->getLine()) << "\n";
        fout << "$\n";
        string str;
        llvm::raw_string_ostream(str) << *usesite;
        fout << str << "\n";
        fout.close();

    }

    void fromVultoAssigntoUse(std::vector<Instruction *> *vulcallsites, std::vector<Instruction *> *assigncallsites, Instruction *assignsite, std::vector<Instruction *> *usecallsites, Instruction *usesite, int filecount, std::string filenameprefix = ""){
        std::vector<Instruction *> cpvulcallsites, cpasscallsites_a;
        std::vector<Instruction *> *PathfromVultoAss = new std::vector<Instruction *>();
        auto smallsize = vulcallsites->size() > assigncallsites->size() ? assigncallsites->size() : vulcallsites->size();
        int i = 0;
        for(; i < smallsize; i++){
            if((*vulcallsites)[i] != (*assigncallsites)[i]){
                break;
            }
        }
        int tmp = i;
        for(; tmp < vulcallsites->size(); tmp++){
            cpvulcallsites.push_back((*vulcallsites)[tmp]);
        }
        tmp = i;
        for(; tmp < assigncallsites->size(); tmp++){
            cpasscallsites_a.push_back((*assigncallsites)[tmp]);
        }
        for(auto idx = cpvulcallsites.size() - 1; idx > 0; idx -= 2){
            PathfromVultoAss->push_back(cpvulcallsites[idx]);
            auto getret = new getRet();
            getret->BBvisit(cpvulcallsites[idx]->getParent(), 0);
            if(getret->found){
                PathfromVultoAss->push_back(getret->ret);
            }else{
                errs() << "unable to find a ret inst!\n";
                return;
            }
            
        }
        PathfromVultoAss->push_back(cpvulcallsites[0]);
        for(auto idx = 1; idx < cpasscallsites_a.size(); idx += 2){
            PathfromVultoAss->push_back(cpasscallsites_a[idx - 1]);
            PathfromVultoAss->push_back(cpasscallsites_a[idx]);
        }

        std::vector<Instruction *> cpasscallsites_b, cpusecallsites;
        std::vector<Instruction *> *PathfromAsstoUse = new std::vector<Instruction *>();
        smallsize = assigncallsites->size() > usecallsites->size() ? usecallsites->size() : assigncallsites->size();
        i = 0;
        for(; i < smallsize; i++){
            if((*assigncallsites)[i] != (*usecallsites)[i]){
                break;
            }
        }
        tmp = i;
        for(; tmp < assigncallsites->size(); tmp++){
            cpasscallsites_b.push_back((*assigncallsites)[tmp]);
        }
        tmp = i;
        for(; tmp < usecallsites->size(); tmp++){
            cpusecallsites.push_back((*usecallsites)[tmp]);
        }
        cpasscallsites_b.push_back(assignsite);
        for(auto idx = cpasscallsites_b.size() - 1; idx > 0; idx -= 2){
            PathfromAsstoUse->push_back(cpasscallsites_b[idx]);
            auto getret = new getRet();
            getret->BBvisit(cpasscallsites_b[idx]->getParent(), 0);
            if(getret->found){
                PathfromAsstoUse->push_back(getret->ret);
            }else{
                errs() << "unable to find a ret inst!\n";
                return;
            }
            
        }
        PathfromAsstoUse->push_back(cpasscallsites_b[0]);
        for(auto idx = 1; idx < cpusecallsites.size(); idx += 2){
            PathfromAsstoUse->push_back(cpusecallsites[idx - 1]);
            PathfromAsstoUse->push_back(cpusecallsites[idx]);
        }

        printPath2(PathfromVultoAss, PathfromAsstoUse, assignsite, usesite, (cpvulcallsites.size() + 1) / 2, (cpasscallsites_b.size() + 1) / 2, filecount, filenameprefix);
    }

    void TaintAnalysisVisitor::visitStoreInst(StoreInst &I) {
#ifdef DEBUG_STORE_INSTR
        dbgs() << "TaintAnalysisVisitor::visitStoreInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        Value *srcPointer = I.getValueOperand();
        std::set<TaintFlag*> *srcTaintInfo = this->getTFs(srcPointer);
        //Get the mem locations to store.
        Value *dstPointer = I.getPointerOperand();
        std::set<PointerPointsTo*> *dstPointsTo = this->getPtos(dstPointer);
        //De-dup
        std::set<PointerPointsTo*> uniqueDstPto;
        if(dstPointsTo && !dstPointsTo->empty()) {
            for (PointerPointsTo *currPointsToObj : *dstPointsTo) {
                long target_field = currPointsToObj->dstfieldId;
                AliasObject *dstObj = currPointsToObj->targetObject;
                auto fdtaintinfo = dstObj->getFieldTaint(target_field);
                if(fdtaintinfo){
                    for(auto taintinfo : fdtaintinfo->targetTaint){
                        if(taintinfo->isTainted() && this->currState.visitedsites.find(&I) == this->currState.visitedsites.end()){
                            errs() << "Store" << "\n";
                            errs() << I.getDebugLoc()->getFilename() << "\n";
                            errs() << I.getDebugLoc()->getLine() << "\n";
                            if(dstPointsTo->size() > 1){
                                bool prior = true;
                                for(auto obj : *dstPointsTo){
                                    bool no_taint = true;
                                    auto fdttinfo = obj->targetObject->getFieldTaint(obj->dstfieldId);
                                    if(fdttinfo){
                                        for(auto ttinfo : fdttinfo->targetTaint){
                                            if(ttinfo->isTainted()){
                                                no_taint = false;
                                            }
                                        }
                                    }
                                    if(no_taint){
                                        prior = false;
                                    }
                                }
                                if(prior){
                                    fromVultoUse(&this->currState.vulsitecontext, this->currFuncCallSites, &I, this->currState.filecounter++, this->currState.printPathDir + "/path2MemWrite-");
                                }else{
                                    if(currPointsToObj->propagatingInst && isa<Instruction>(currPointsToObj->propagatingInst->inst)){
                                        fromVultoAssigntoUse(&this->currState.vulsitecontext, currPointsToObj->propagatingInst->ctx, dyn_cast<Instruction>(currPointsToObj->propagatingInst->inst), this->currFuncCallSites, &I, this->currState.filecounter++, this->currState.printPathDir + "/path2MemWrite-");
                                        }
                                    }
                            }else{
                                fromVultoUse(&this->currState.vulsitecontext, this->currFuncCallSites, &I, this->currState.filecounter++, this->currState.printPathDir + "/path2MemWrite-");
                            }
                            this->currState.visitedsites.insert(&I);
                        }
                    }
                }
                if (std::find_if(uniqueDstPto.begin(),uniqueDstPto.end(),[currPointsToObj](const PointerPointsTo *pto){
                    return currPointsToObj->pointsToSameObject(pto);
                }) == uniqueDstPto.end())
                {
                    uniqueDstPto.insert(currPointsToObj);
                }
            }
        }
#ifdef DEBUG_STORE_INSTR
        dbgs() << "TaintAnalysisVisitor::visitStoreInst: #targetMemLoc: " << uniqueDstPto.size() << "\n";
#endif
        if (uniqueDstPto.empty()) {
            //Nowhere to taint..
            return;
        }
        bool multi_pto = (uniqueDstPto.size() > 1); 
        //Prepare either the taint flags or the taint kill, and their mapping to the taint dst.
        std::set<TaintFlag*> newTaintInfo;
        //The mapping between the taint dst and the TFs to propagate.
        std::map<PointerPointsTo*,std::set<TaintFlag*>> taintMap;
        if (srcTaintInfo && !srcTaintInfo->empty()) {
            //The src value is tainted, then we need to propagate the taint flags;
            TaintAnalysisVisitor::makeTaintInfoCopy(&I,srcTaintInfo,&newTaintInfo);
            //Try to set up the mapping between the taint flags and the taint dst if there are more than one dst.
            if (multi_pto) {
                inferTaintMap(I,&newTaintInfo,&uniqueDstPto,taintMap);
            }
        }else {
            //It's not tainted, then this is actually a taint kill if (1) there is only one target 
            //mem location (otherwise this is a weak taint kill that we will not honor to be conservative). 
            //and (2) the target mem location is tainted now (otherwise no need to kill). 
            //If so then we also need to propagate the taint kill flag.
            if (!multi_pto) {
                //Create a taint kill flag.
                TaintFlag *tf = new TaintFlag(this->makeInstLoc(&I),false,nullptr,false);
                newTaintInfo.insert(tf);
            }
        }
#ifdef DEBUG_STORE_INSTR
        dbgs() << "TaintAnalysisVisitor::visitStoreInst: #newTaintInfo: " << newTaintInfo.size() << "\n";
#endif
        if (newTaintInfo.empty()) {
            return;
        }
        //Ok now propagate the taint flags to the target mem locs, according to the mapping set up previously.
        std::set<TaintFlag*> addedTFs;
        for (PointerPointsTo *pto : uniqueDstPto) {
            std::set<TaintFlag*> *toAdd = (taintMap.find(pto) == taintMap.end() ? &newTaintInfo : &(taintMap[pto]));
            for (TaintFlag *tf : *toAdd) {
                //Don't forget the "is_weak" flag in the TF indicating whether it's a strong or weak taint.
                //If the "tf" is already a weak taint, then even there is only one pointee, it's still weak;
                //If the "tf" is strong but there are multiple pointees, then again weak;
                tf->is_weak |= multi_pto;
                if (pto->targetObject->addFieldTaintFlag(pto->dstfieldId,tf)) {
                    addedTFs.insert(tf);
                }
            }
        }
        //Free the memory occupied by the unuseful TFs (e.g. duplicated in the dst mem loc).
        if (addedTFs.size() < newTaintInfo.size()) {
            for (TaintFlag *tf : newTaintInfo) {
                if (addedTFs.find(tf) == addedTFs.end()) {
                    delete(tf);
                }
            }
        }
    }

    // The following instructions are ignored.
    // we will deal with them, if we find them
    void TaintAnalysisVisitor::visitVAArgInst(VAArgInst &I) {
        // NO idea how to handle this
        assert(false);
    }

    void TaintAnalysisVisitor::visitVACopyInst(VACopyInst &I) {
        // No idea how to handle this
        //assert(false);
    }

    void TaintAnalysisVisitor::setupCallContext(CallInst &I, Function *currFunction,
                                                std::vector<Instruction*> *newCallContext) {

        std::map<Value*, std::set<TaintFlag*>*> *contextTaintInfo = currState.getTaintInfo(newCallContext);
        unsigned int arg_no = 0;

        for (User::op_iterator arg_begin = I.arg_begin(), arg_end = I.arg_end(); arg_begin != arg_end; arg_begin++) {
            //errs() << "entered 1 time " << "\n";
            Value *currArgVal =(*arg_begin).get();
            std::set<TaintFlag*> *currArgTaintInfo = this->getTFs(currArgVal);
            if (!currArgTaintInfo || currArgTaintInfo->empty()) {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "TaintAnalysisVisitor::setupCallContext(): arg " << arg_no << " does not have taint info.\n";
#endif
                arg_no++;
                continue;
            }
#ifdef DEBUG_CALL_INSTR
            dbgs() << "TaintAnalysisVisitor::setupCallContext(): arg " << arg_no << " #TF: " << currArgTaintInfo->size() << "\n";
#endif
            unsigned int farg_no = 0;
            for (Function::arg_iterator farg_begin = currFunction->arg_begin(), farg_end = currFunction->arg_end();
                 farg_begin != farg_end; farg_begin++) 
            {
                Value *currfArgVal = &(*farg_begin);
                if (farg_no == arg_no) {
                    std::set<TaintFlag*> *tfs = this->makeTaintInfoCopy(&I, currArgTaintInfo);
                    if (tfs && !tfs->empty()) {
#ifdef DEBUG_CALL_INSTR
                        // OK, we need to add taint info.
                        dbgs() << "TaintAnalysisVisitor::setupCallContext(): farg " << arg_no << " has #TF: " << tfs->size() << "\n";
#endif
                        (*contextTaintInfo)[currfArgVal] = tfs;
                    }
                    break;
                }
                ++farg_no;
            }
            ++arg_no;
        }
    }

    void TaintAnalysisVisitor::propagateTaintToMemcpyArguments(std::vector<long> &memcpyArgs, CallInst &I) {
#ifdef DEBUG_CALL_INSTR
        dbgs() << "Processing memcpy function\n";
#endif
        //TODO: does it really make sense to propagate taint from the src pointer value (not the pointee) to the dst?
        // we do not need any special taint handling..because alias takes care of propagating
        // the pointee memory content, here we just need to update taint of the arguments.
        // get src operand
        Value *srcOperand = I.getArgOperand((unsigned int) memcpyArgs[0]);
        // get dst operand
        Value *dstOperand = I.getArgOperand((unsigned int) memcpyArgs[1]);

        std::set<Value*> mergeVals;
        mergeVals.insert(srcOperand);

        std::set<TaintFlag*>* newTaintInfo = this->mergeTaintInfo(mergeVals, &I);
        if(newTaintInfo != nullptr) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Trying to memcpy from tainted argument\n";
#endif
            this->updateTaintInfo(dstOperand, newTaintInfo);
        }
    }

    void TaintAnalysisVisitor::handleKernelInternalFunction(CallInst &I, Function *currFunc) {
        //NOTE: taint initiator function like copy_from_user has been handled in AliasAnalysis, including the taint propagation.
        if (TaintAnalysisVisitor::functionChecker->is_memcpy_function(currFunc)) {
            // Handle memcpy function..
            // get memcpy argument numbers
            std::vector<long> memcpyArgs = TaintAnalysisVisitor::functionChecker->get_memcpy_arguments(currFunc);
            //propagate taint from src to dst.
            this->propagateTaintToMemcpyArguments(memcpyArgs, I);
        }else if (TaintAnalysisVisitor::functionChecker->is_atoi_function(currFunc)) {
            // This is an atoi like function?
            // if yes? get the taint of the object pointed by the first argument.
            // propagate that to the return value.
            std::set<TaintFlag*> allPointerTaint;
            allPointerTaint.clear();
            this->getPtrTaintInfo(I.getArgOperand(0), allPointerTaint, &I);
            if (!allPointerTaint.empty()) {
                std::set<TaintFlag*> *newTaintSet = this->makeTaintInfoCopy(&I, &allPointerTaint);
                this->updateTaintInfo(&I, newTaintSet);
            }
        }else if (TaintAnalysisVisitor::functionChecker->is_sscanf_function(currFunc)) {
            // This is a sscanf function?
            // if yes? get the taint of the object pointed by the first argument.
            std::set<TaintFlag*> allPointerTaint;
            allPointerTaint.clear();
            this->getPtrTaintInfo(I.getArgOperand(0), allPointerTaint, &I);
            if (!allPointerTaint.empty()) {
                std::set<TaintFlag*> *newTaintSet = this->makeTaintInfoCopy(&I, &allPointerTaint);
                std::set<TaintFlag*> addedTaints;
                // now add taint to all objects pointed by the arguments.
                unsigned int arg_idx;
                for (arg_idx = 2; arg_idx < I.getNumArgOperands(); arg_idx++) {
                    Value *argVal = I.getArgOperand(arg_idx);
                    std::set<PointerPointsTo*> *currPtsTo = PointsToUtils::getPointsToObjects(this->currState, this->currFuncCallSites, argVal);
                    if (currPtsTo != nullptr) {
                        //Set "is_weak"
                        bool multi_pto = (currPtsTo->size() > 1);
                        for(auto currT : *newTaintSet) {
                            if (currT) {
                                currT->is_weak |= multi_pto;
                            }
                        }
                        for(auto currP : *currPtsTo) {
                            for(auto currT : *newTaintSet) {
                                if(currP->targetObject->addFieldTaintFlag(currP->dstfieldId, currT)) {
                                    addedTaints.insert(currT);
                                }
                            }
                        }
                    }
                }
                //Free memory.
                for (auto currT : *newTaintSet) {
                    if (addedTaints.find(currT) == addedTaints.end()) {
                        delete(currT);
                    }
                }
                delete(newTaintSet);
            }
        }else {
            // TODO (below):
            // untaint all the arguments, depending on whether we are indeed calling kernel internal functions.
            // memset()?
        }
    }

    VisitorCallback* TaintAnalysisVisitor::visitCallInst(CallInst &I, Function *currFunc,
                                                         std::vector<Instruction *> *oldFuncCallSites,
                                                         std::vector<Instruction *> *callSiteContext) {
#ifdef DEBUG_CALL_INSTR
        dbgs() << "TaintAnalysisVisitor::visitCallInst(): " << InstructionUtils::getValueStr(&I) << "\n";
#endif
        // if this is a kernel internal function.
        if(currFunc->isDeclaration()) {
            this->handleKernelInternalFunction(I, currFunc);
            return nullptr;
        }

        // else, we need to setup taint context and create a new visitor.
        setupCallContext(I, currFunc, callSiteContext);

        // create a new TaintAnalysisVisitor
        TaintAnalysisVisitor *vis = new TaintAnalysisVisitor(currState, currFunc, callSiteContext);

        //debugInstTaint(I);

        return vis;
    }

    void TaintAnalysisVisitor::stitchChildContext(CallInst &I, VisitorCallback *childCallback) {
        // just connect the taint of the return values.
        TaintAnalysisVisitor *vis = (TaintAnalysisVisitor *)childCallback;
        if(vis->retValTaints.size() > 0 ){
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Stitching return value for call instruction:";
            I.print(dbgs());
            dbgs() << "\n";
#endif
            // create new taint info.
            std::set<TaintFlag*>* newTaintInfo = new std::set<TaintFlag*>();
            for(auto currRetTaint:vis->retValTaints) {
                //NOTE: ret taint must be able to reach this call site, so no need for the taint path check.
                TaintFlag *newTaintFlag = new TaintFlag(currRetTaint, this->makeInstLoc(&I));
                newTaintInfo->insert(newTaintInfo->end(), newTaintFlag);
            }

            //update taint info
            updateTaintInfo(&I, newTaintInfo);
        }
    }

    void TaintAnalysisVisitor::visitReturnInst(ReturnInst &I) {
        // add taint of the return value to the retTaintInfo set.
        Value *targetRetVal = I.getReturnValue();
        if (!targetRetVal) {
            return;
        }
        std::set<TaintFlag*> *currRetTaintInfo = this->getTFs(targetRetVal);
        if (!currRetTaintInfo || currRetTaintInfo->empty()) {
#ifdef DEBUG_RET_INSTR
            dbgs() << "Return value: " << InstructionUtils::getValueStr(&I) << ", does not have TaintFlag.\n";
#endif
            return;
        }
        for(auto a : *currRetTaintInfo) {
            if(std::find_if(this->retValTaints.begin(), this->retValTaints.end(), [a](const TaintFlag *n) {
                return  n->isTaintEquals(a);
            }) == this->retValTaints.end()) {
                // if not insert the new taint flag into the newTaintInfo.
                this->retValTaints.insert(this->retValTaints.end(), a);
            }
        }
    }

    void TaintAnalysisVisitor::visitICmpInst(ICmpInst &I) {
        // merge taint flag of all the operands.
        std::set<Value*> allVals;
        for(unsigned i=0;i<I.getNumOperands(); i++) {
            Value* currOp = I.getOperand(i);
            allVals.insert(currOp);
        }
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }
    }

#ifdef CONTROL_TAINT
    //hz: add support for branch and switch instructions into taint analysis. 
    //TODO: In the future if we want to do control taint, we need to extend these below methods.

    //hz: the overall propagation logic of this is borrowed (w/o a plan to return) from visitCastInst.
    void TaintAnalysisVisitor::visitBranchInst(BranchInst &I) {
        //No need to handle a unconditional branch since it has no condition variable.
        if (I.isUnconditional()) {
            return;
        }
        //Get the branch condition Value.
        Value *condition = I.getCondition();
        std::set<TaintFlag*> *srcTaintInfo = this->getTFs(condition);
        // if there exists some taintflags..propagate them
        if (srcTaintInfo && !srcTaintInfo->empty()) {
            std::set<TaintFlag*> *newTaintInfo = this->makeTaintInfoCopy(&I, srcTaintInfo);
            if (newTaintInfo != nullptr) {
                this->updateTaintInfo(&I, newTaintInfo);
            }
        }
    }

    /*
    void TaintAnalysisVisitor::visitIndirectBrInst(IndirectBrInst &I) {
        //
    }
    */

    //hz: basically the same as visitBranchInst()
    void TaintAnalysisVisitor::visitSwitchInst(SwitchInst &I) {
        //Get the switch condition Value.
        Value *condition = I.getCondition();
        std::set<TaintFlag*> *srcTaintInfo = this->getTFs(condition);
        // if there exists some taintflags..propagate them
        if (srcTaintInfo && !srcTaintInfo->empty()) {
            std::set<TaintFlag*> *newTaintInfo = this->makeTaintInfoCopy(&I, srcTaintInfo);
            if (newTaintInfo && !newTaintInfo->empty()) {
                this->updateTaintInfo(&I, newTaintInfo);
            }
        }
    }
#endif

}
