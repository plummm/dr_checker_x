//
// Created by machiry on 8/23/16.
//

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "../../Utils/include/InstructionUtils.h"
#include <vector>

#ifndef PROJECT_TAINTFLAG_H
#define PROJECT_TAINTFLAG_H
using namespace llvm;
namespace DRCHECKER {

    //hz: Class that intends to identify a unique taint source.
    class TaintTag {
    public:
        long fieldId;
        Value *v;

        TaintTag(long fieldId, Value *v) {
            this -> fieldId = fieldId;
            this -> v = v;
        }

        TaintTag(TaintTag *srcTag) {
            this -> fieldId = srcTag -> fieldId;
            this -> v = srcTag -> v;
        }

        bool isTagEquals(TaintTag *dstTag) {
            if (!dstTag){
                return false;
            }
            if (this == dstTag){
                return true;
            }
            return this->fieldId == dstTag->fieldId &&
                   this->v == dstTag->v;
        }
    };

    //Class that holds the taint flag
    class TaintFlag {

    public:
        //Constructors
        TaintFlag(Value *targetInstr, bool is_tainted) {
            assert(targetInstr != nullptr && "Target Instruction cannot be NULL");
            this->targetInstr = targetInstr;
            this->is_tainted = is_tainted;
            this->tag = nullptr;
        }

        TaintFlag(TaintFlag *copyTaint, Value *targetInstr, Value *srcOperand) {
            this->targetInstr = targetInstr;
            this->is_tainted = copyTaint->isTainted();
            // copy the instruction trace from the source taint guy
            this->instructionTrace.insert(instructionTrace.begin(),
                                          copyTaint->instructionTrace.begin(), copyTaint->instructionTrace.end());
            //hz: in case the instructionTrace is empty
            Instruction *lastInstr = nullptr;
            if (!instructionTrace.empty()){
                lastInstr = this->instructionTrace.back();
            }

            // add the source instruction into the trace.
            Instruction *srcInstr = dyn_cast<Instruction>(srcOperand);
            if(srcInstr != nullptr && lastInstr != srcInstr) {
                this->instructionTrace.push_back(srcInstr);
            }
            //hz: tag propagation.
            this->tag = copyTaint->tag;
        }

        //hz: A copy w/ a different tag.
        TaintFlag(TaintFlag *copyTaint, TaintTag *tag) {
            this->targetInstr = copyTaint -> targetInstr;
            this->is_tainted = copyTaint->isTainted();
            // copy the instruction trace from the source taint guy
            this->instructionTrace.insert(instructionTrace.begin(),
                                          copyTaint->instructionTrace.begin(), copyTaint->instructionTrace.end());
            this->tag = tag;
        }

        TaintFlag(Value * targetInstr) : TaintFlag(targetInstr, false) {}
        //Destructors
        ~TaintFlag() {}

        bool isTainted() const {
            return is_tainted;
        }

        bool isTaintEquals(const TaintFlag *dstTaint) const {
            if(dstTaint != nullptr) {
                //hz: we don't care about in which specific paths the targetInst is tainted, what really matters
                //are below properties:
                //(1) the targetInst of this taintFlag
                //(2) whether it's tainted or not
                //(3) the taint source, which is wrapped in our TaintTag class.
                //These are properties we consider when comparing two taint flags.
                //Property (1) and (2)
                if(this->targetInstr != dstTaint->targetInstr || this->isTainted() != dstTaint->isTainted()){
                    return false;
                }
                //Property (3):
                if(this->tag && dstTaint->tag){
                    return this->tag->isTagEquals(dstTaint->tag);
                }else if(this->tag || dstTaint->tag){
                    //One has tag but the other doesn't.
                    return false;
                }
                return true;
            }
            return false;
        }

        void addInstructionToTrace(Instruction *toAdd) {
            if(this->instructionTrace.size() > 0) {
                // check if last instruction is the current instruction.
                Instruction *lastInstr = this->instructionTrace.back();
                if (toAdd == lastInstr) {
                    return;
                }
            }
            this->instructionTrace.push_back(toAdd);
        }

        Value *targetInstr;
        // trace of instructions that resulted in this taint.
        std::vector<Instruction *> instructionTrace;
        void dumpInfo(raw_ostream &OS) {

            //OS << "Taint Flag for:";
            //this->targetInstr->print(OS);
            //OS << ", Tainted=" << this->isTainted() << "\n";
            OS << " Instruction Trace: [";
            for(std::vector<Instruction *>::iterator SI = this->instructionTrace.begin(); SI != this->instructionTrace.end(); ++SI) {
                AAMDNodes targetMDNodes;
                (*SI)->getAAMetadata(targetMDNodes, true);
                OS << (InstructionUtils::getInstructionName((*SI))) << ": at line " << InstructionUtils::getLineNumber(**SI) << " ,";
            }
            OS << "]\n";
            //hz: dump tag information if any.
            if (tag) {
                OS << "Taint Tag:\n";
                OS << "Value:\n";
                tag->v->print(OS,true);
                OS << "\nfieldId: " << tag->fieldId << " \n";
            }

        }

        //hz: add taint tag support.
        TaintTag *tag;
    private:
        // flag to indicate the taint flag.
        bool is_tainted;

    };

    /***
     * Class that represents taint of an object field.
     */
    class FieldTaint {
    public:
        long fieldId;
        std::set<TaintFlag *> targetTaint;

        FieldTaint(long srcField) {
            this->fieldId = srcField;
        }

        ~FieldTaint() {
            //TODO: implement this in a smart way.
            /*for(auto currT:targetTaint) {
                delete(currT);
            }*/
        }

        bool addTaintFlag(TaintFlag *toAdd) {
            // check if the set already contains same taint?
            if(std::find_if(targetTaint.begin(), targetTaint.end(), [toAdd](const TaintFlag *n) {
                return  n->isTaintEquals(toAdd);
            }) == targetTaint.end()) {
                // if not insert the new taint flag into the newTaintInfo.
                targetTaint.insert(targetTaint.end(), toAdd);
                return true;
            }
            return false;
        }

    };

}

#endif //PROJECT_TAINTFLAG_H
