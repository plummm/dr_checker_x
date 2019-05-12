//
// Created by machiry on 12/5/16.
//

#include <set>
#include <llvm/IR/CFG.h>
#include "InstructionUtils.h"

using namespace llvm;

namespace DRCHECKER {


    bool InstructionUtils::isPointerInstruction(Instruction *I) {
        bool retVal = false;
        LoadInst *LI = dyn_cast<LoadInst>(I);
        if(LI) {
            retVal = true;
        }
        StoreInst *SI = dyn_cast<StoreInst>(I);
        if(SI) {
            retVal = true;
        }
        VAArgInst *VAAI = dyn_cast<VAArgInst>(I);
        if(VAAI) {
            retVal = true;
        }
        return retVal;
    }

    unsigned InstructionUtils::getLineNumber(Instruction &I)
    {

        const DebugLoc &currDC = I.getDebugLoc();
        if(currDC) {
            return currDC.getLine();
        }
        return -1;
    }

    std::string InstructionUtils::getInstructionName(Instruction *I) {
        if(I->hasName()) {
            return I->getName().str();
        } else {
            return "N/A";
        }
    }

    std::string InstructionUtils::getValueName(Value *v) {
        if(v->hasName()) {
            return v->getName().str();
        } else {
            return "No Name";
        }
    }

    std::string InstructionUtils::escapeJsonString(const std::string& input) {
        std::ostringstream ss;
        for (auto iter = input.cbegin(); iter != input.cend(); iter++) {
            //C++98/03:
            for (std::string::const_iterator iter = input.begin(); iter != input.end(); iter++) {
                switch (*iter) {
                    case '\\':
                        ss << "\\\\";
                        break;
                    case '"':
                        ss << "\\\"";
                        break;
                    case '/':
                        ss << "\\/";
                        break;
                    case '\b':
                        ss << "\\b";
                        break;
                    case '\f':
                        ss << "\\f";
                        break;
                    case '\n':
                        ss << "\\n";
                        break;
                    case '\r':
                        ss << "\\r";
                        break;
                    case '\t':
                        ss << "\\t";
                        break;
                    default:
                        ss << *iter;
                        break;
                }
            }
            return ss.str();
        }
    }

    std::string InstructionUtils::escapeValueString(Value *currInstr) {
        return InstructionUtils::escapeJsonString(InstructionUtils::getValueStr(currInstr));
    }

    DILocation* getRecursiveDILoc(Instruction *currInst, std::string &funcFileName, std::set<BasicBlock*> &visitedBBs) {
        DILocation *currIL = currInst->getDebugLoc().get();
        if(funcFileName.length() == 0) {
            return currIL;
        }
        if(currIL != nullptr && currIL->getFilename().equals(funcFileName)) {
            return currIL;
        }

        BasicBlock *currBB = currInst->getParent();
        if(visitedBBs.find(currBB) != visitedBBs.end()) {
            return nullptr;
        }
        for(auto &iu :currBB->getInstList()) {
            Instruction *currIterI = &iu;
            DILocation *currIteDL = currIterI->getDebugLoc();
            if(currIteDL != nullptr && currIteDL->getFilename().equals(funcFileName)) {
                return currIteDL;
            }
            if(currIterI == currInst) {
                break;
            }
        }

        visitedBBs.insert(currBB);


        for (auto it = pred_begin(currBB), et = pred_end(currBB); it != et; ++it) {
            BasicBlock* predecessor = *it;
            DILocation *currBBLoc = getRecursiveDILoc(predecessor->getTerminator(), funcFileName, visitedBBs);
            if(currBBLoc != nullptr) {
                return currBBLoc;
            }
        }
        return nullptr;
    }

    std::string getFunctionFileName(Function *F) {
        SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
        F->getAllMetadata(MDs);
        for (auto &MD : MDs) {
            if (MDNode *N = MD.second) {
                if (auto *subProgram = dyn_cast<DISubprogram>(N)) {
                    return subProgram->getFilename();
                }
            }
        }
        return "";
    }


    DILocation* InstructionUtils::getCorrectInstrLocation(Instruction *I) {
        DILocation *instrLoc = I->getDebugLoc().get();
        //BasicBlock *firstBB = &(I->getFunction()->getEntryBlock());
        //Instruction *firstInstr = firstBB->getFirstNonPHIOrDbg();

        //DILocation *firstIL = firstInstr->getDebugLoc().get();
        std::set<BasicBlock*> visitedBBs;
        std::string funcFileName = getFunctionFileName(I->getFunction());


        if(instrLoc != nullptr && instrLoc->getFilename().endswith(".c")) {
            return instrLoc;
        }

        if(instrLoc == nullptr || (funcFileName.length() > 0  && !instrLoc->getFilename().equals(funcFileName))) {
            // OK, the instruction is from the inlined function.
            visitedBBs.clear();
            DILocation *actualLoc = getRecursiveDILoc(I, funcFileName, visitedBBs);
            if(actualLoc != nullptr) {

                return actualLoc;
            }
        }

        return instrLoc;
    }

    int InstructionUtils::getInstrLineNumber(Instruction *I) {
        DILocation *targetLoc = InstructionUtils::getCorrectInstrLocation(I);
        if(targetLoc != nullptr) {
            return targetLoc->getLine();
        }
        return -1;
    }

    void InstructionUtils::printInst(Instruction *I, raw_ostream &ROS) {
        static std::map<Instruction*,std::string> InstPrintMap;
        if (!I){
            return;
        }
        if (InstPrintMap.find(I) != InstPrintMap.end()){
            ROS << InstPrintMap[I];
            return;
        }
        std::string str;
        llvm::raw_string_ostream OS(str);
        //Inst, BB, Function, and File
        std::string& inst = InstructionUtils::getValueStr(dyn_cast<Value>(I));
        OS << inst << " ,BB: ";
        if (I->getParent()) {
            OS << InstructionUtils::getBBStrID(I->getParent());
        }
        OS << " ,FUNC: ";
        if (I->getFunction()) {
            OS << I->getFunction()->getName().str();
        }
        OS << " ,SRC: ";
        DILocation *instrLoc = InstructionUtils::getCorrectInstrLocation(I);
        if (instrLoc != nullptr) {
            OS << InstructionUtils::escapeJsonString(instrLoc->getFilename());
            OS << " @ " << instrLoc->getLine();
        } else {
            OS << "N/A";
        }
        OS << "\n";
        InstPrintMap[I] = OS.str();
        ROS << OS.str();
    }

    LOC_INF* InstructionUtils::getInstStrRep(Instruction *I) {
        if(!I){
            return nullptr;
        }
        std::string inst,bb,func,mod;
        inst = InstructionUtils::getValueStr(dyn_cast<Value>(I));
        if(I->getParent()){
			bb = InstructionUtils::getBBStrID(I->getParent());
        }
        if(I->getFunction()){
            func = I->getFunction()->getName().str();
        }
        if(I->getModule()){
            mod = I->getModule()->getName().str();
        }
        LOC_INF *str_inst = new LOC_INF;
        str_inst->push_back(inst);
        str_inst->push_back(bb);
        str_inst->push_back(func);
        str_inst->push_back(mod);
        return str_inst;
    }

    std::vector<LOC_INF>* InstructionUtils::getStrCtx(std::vector<Instruction*> *callSites) {
        std::vector<LOC_INF> *pvec = new std::vector<LOC_INF>();
        for(Instruction *currCallSite : *callSites) {
            LOC_INF *str_inst = InstructionUtils::getInstStrRep(currCallSite);
            if(str_inst){
                pvec->push_back(*str_inst);
            }
        }
        return pvec;
    }

    std::string& InstructionUtils::getBBStrID(BasicBlock* B) {
        static std::map<BasicBlock*,std::string> BBNameMap;
        if (BBNameMap.find(B) == BBNameMap.end()) {
            if (B) {
                if (!B->getName().empty()){
                    BBNameMap[B] = B->getName().str();
                }else{
    	            std::string Str;
    	            raw_string_ostream OS(Str);
    	            B->printAsOperand(OS, false);
                    BBNameMap[B] = OS.str();
                }
            }else{
                BBNameMap[B] = "";
            }
        }
        return BBNameMap[B];
    }

    //Set up a cache for the expensive "print" operation.
    std::string& InstructionUtils::getValueStr(Value *v) {
        static std::map<Value*,std::string> ValueNameMap;
        if (ValueNameMap.find(v) == ValueNameMap.end()) {
            if(v){
                std::string str;
                llvm::raw_string_ostream ss(str);
                ss << *v;
                ValueNameMap[v] = ss.str();
            }else{
                ValueNameMap[v] = "";
            }
        }
        return ValueNameMap[v];
    }

    //Set up a cache for the expensive "print" operation specifically for Type.
    std::string& InstructionUtils::getTypeStr(Type *v) {
        static std::map<Type*,std::string> TypeNameMap;
        if (TypeNameMap.find(v) == TypeNameMap.end()) {
            if(v){
                std::string str;
                llvm::raw_string_ostream ss(str);
                ss << *v;
                TypeNameMap[v] = ss.str();
            }else{
                TypeNameMap[v] = "";
            }
        }
        return TypeNameMap[v];
    }

}
