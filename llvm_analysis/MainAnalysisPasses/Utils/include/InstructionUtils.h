//
// Created by machiry on 8/23/16.
//

#ifndef PROJECT_INSTRUCTIONUTILS_H
#define PROJECT_INSTRUCTIONUTILS_H
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/IR/Operator.h"
#include <string>
#include <sstream>
#include "../../SoundyAliasAnalysis/include/ResType.h"

using namespace llvm;

namespace DRCHECKER {
    
    class FieldDesc {
        public:
        int bitoff = 0;
        //host_tys and fid: from innermost to outermost.
        std::vector<Type*> tys, host_tys;
        std::vector<unsigned> fid;

        FieldDesc() {
            this->bitoff = 0;
            return;
        }

        FieldDesc(FieldDesc *fd) {
            if (!fd)
                return;
            this->bitoff = fd->bitoff;
            this->tys = fd->tys;
            this->host_tys = fd->host_tys;
            this->fid = fd->fid;
        }

        void print(raw_ostream &OS);

        //Whether a certain type is in the "tys" list.
        int findTy(Type *ty);

        int findHostTy(Type *ty);
    };

    class CandStructInf {
        public:
        std::vector<FieldDesc*> *fds;
        std::vector<int> ind;
        int score = 0;
    };

    class InstructionUtils {
        public:
        /***
         *  Is any of the operands to the instruction is a pointer?
         * @param I  Instruction to be checked.
         * @return  true/false
         */
        static bool isPointerInstruction(Instruction *I);

        /***
         *  Get the line number of the instruction.
         * @param I instruction whose line number need to be fetched.
         * @return unsigned int representing line number.
         */
        static unsigned getLineNumber(Instruction &I);

        /***
         *  Get the name of the provided instruction.
         * @param I instruction whose name needs to be fetched.
         * @return string representing the instruction name.
         */
        static std::string getInstructionName(Instruction *I);

        /***
         * Get the name of the provided value operand.
         * @param v The value operand whose name needs to be fetched.
         * @return string representing name of the provided value.
         */
        static std::string getValueName(Value *v);

        /***
         *  Method to convert string to be json friendly.
         *  Copied from: https://stackoverflow.com/questions/7724448/simple-json-string-escape-for-c
         * @param input input string
         * @return converted string.
         */
        static std::string escapeJsonString(const std::string& input);

        /***
         * Method to convert the provided value to escaped json string.
         *
         * @param currInstr Value object which needs to be converted to json string.
         * @return Converted string.
         */
        static std::string escapeValueString(Value *currInstr);

        /***
         * Get the instruction line number corresponding to the provided instruction.
         * @param I Instruction whose line number needs to be fetched.
         * @return Line number.
         */
        static int getInstrLineNumber(Instruction *I);

        /***
         * Get the correct Debug Location (handles in lineing) for the provided instruction.
         *
         * @param I instruction whose correct debug location needs to be fetched.
         * @return DILocation correct debug location corresponding to the provided instruction.
         */
        static DILocation* getCorrectInstrLocation(Instruction *I);

        //Print the instruction with detailed src level debug info (e.g. file, line number).
        static void printInst(Instruction *I, raw_ostream &OS);

        //Get a string representation of the instruction, including the str of the inst,bb,func,and module.
        static LOC_INF* getInstStrRep(Instruction *I);

        //Get LOC_INF vector for a call context.
        static std::vector<LOC_INF>* getStrCtx(std::vector<Instruction*> *callSites);

        //If the BB has a name then return it, otherwise return its numeric ID as shown in ".ll".
        static std::string& getBBStrID(BasicBlock*);

        //If the BB has a name then return it, otherwise return its order within its parent function BB iteration.
        static std::string& getBBStrID_No(BasicBlock*);
        static std::string& getInstStrID_No(Instruction*);

        //Set up a cache for the expensive "print" operation for llvm::Value.
        static std::string& getValueStr(Value *v);

        //Set up a cache for the expensive "print" operation for llvm::Type.
        static std::string& getTypeStr(Type*);

        static bool isScalar(Value*);

        static int getConstantValue(Constant*,TRAIT*);

        static Value *stripAllCasts(Value*,bool);

        static void stripFuncNameSuffix(std::string *fn);

        static std::string getCalleeName(CallInst*,bool);

        static bool same_types(Type*,Type*);

        //Get the "cmd" arg values of the ioctl() that can reach the target "inst" under the context "ctx".
        static std::set<uint64_t> *getCmdValues(std::vector<Instruction*> *ctx, Instruction* inst, std::map<BasicBlock*,std::set<uint64_t>> *switchMap);

        static std::map<ConstantAggregate*,std::set<long>> *getUsesInStruct(Value *v);

        //Create a new GEP from an existing one, using only the first few indices.
        static GetElementPtrInst *createSubGEP(GEPOperator*,unsigned);

        static bool isAsanInst(Instruction *inst);

        static Instruction *isAsanReportBB(BasicBlock *bb);

        static bool isPotentialAsanInst(Instruction *inst);

        static std::vector<FieldDesc*> *getCompTyDesc(DataLayout *dl, CompositeType *ty);

        static bool isTyUsedByFunc(Type *ty, Function *func);

        static bool isIndexValid(Type *ty, unsigned fid);

        //Given a type's type desc vector, locate the first desc node for a specified field "fid",
        //returning the index of this desc node within the vector.
        static int locateFieldInTyDesc(std::vector<FieldDesc*> *tydesc, unsigned fid);

        //Given a type's type desc vector, locate the first desc node for a specified bit offset,
        //returning the index of this desc node within the vector.
        static int locateBitsoffInTyDesc(std::vector<FieldDesc*> *tydesc, int boff);
    };

}
#endif //PROJECT_INSTRUCTIONUTILS_H
