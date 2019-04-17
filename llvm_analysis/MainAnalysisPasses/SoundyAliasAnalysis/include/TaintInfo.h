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

#define DEBUG_INSERT_MOD_INST

    //hz: Class that intends to identify a unique taint source.
    class TaintTag {
    public:
        long fieldId;
        Value *v;
        Type *type;
        //Record all instructions (w/ its call context) that can possibly modify this taint source.
        std::map< Instruction *, std::vector<std::vector<Instruction*>*> > mod_insts;

        TaintTag(long fieldId, Value *v) {
            this -> fieldId = fieldId;
            this -> v = v;
            this -> type = this->getTy();
        }

        TaintTag(TaintTag *srcTag) {
            this -> fieldId = srcTag -> fieldId;
            this -> v = srcTag -> v;
            this -> type = srcTag -> type;
            //This is content copy.
            this -> mod_insts = srcTag -> mod_insts;
        }

        Type *getTy() {
            if (!this->v){
                return nullptr;
            }
            Type *ty = this->v->getType();
            if (ty->isPointerTy()){
                ty = ty->getPointerElementType();
            }
            if (ty->isStructTy() && this->fieldId < ty->getStructNumElements() && this->fieldId >= 0){
                return ty->getStructElementType(this->fieldId);
            }
            return ty;
        }

        bool isTagEquals(TaintTag *dstTag) {
            if (!dstTag){
                return false;
            }
            if (this == dstTag){
                return true;
            }
            //No need to compare mod_insts here since it's determined by other two fields.
            return this->fieldId == dstTag->fieldId &&
                   this->v == dstTag->v;
        }

        void insertModInst(Instruction *inst, std::vector<Instruction *> *call_ctx) {
            if (!inst){
#ifdef DEBUG_INSERT_MOD_INST
                dbgs() << "insertModInst: null inst\n";
#endif
                return;
            }
            std::vector<std::vector<Instruction*>*> *ctx_list;
            if (this->mod_insts.find(inst) == this->mod_insts.end()){
                //No records of this store inst yet.
                ctx_list = new std::vector<std::vector<Instruction*>*>();
                this->mod_insts[inst] = *ctx_list;
#ifdef DEBUG_INSERT_MOD_INST
                dbgs() << "insertModInst: inst inserted!\n";
#endif
            }
            //Detect duplicated call contexts.
            if (call_ctx){
                ctx_list = &(this->mod_insts[inst]);
                if(std::find_if(ctx_list->begin(), ctx_list->end(), [call_ctx](const std::vector<Instruction*> *ctx) {
                    if (ctx->size() != call_ctx->size()){
                        return false;
                    }
                    return (*ctx) == (*call_ctx);
                }) == ctx_list->end()) {
                    //Unique context, insert.
                    //Make a copy of the passed call context vector since it may be changed.
                    std::vector<Instruction*> *new_ctx = new std::vector<Instruction*>();
                    new_ctx->insert(new_ctx->end(),call_ctx->begin(),call_ctx->end());
                    ctx_list->push_back(new_ctx);
#ifdef DEBUG_INSERT_MOD_INST
                    dbgs() << "insertModInst: ctx inserted!\n";
#endif
                }
            }
        }

        void dumpInfo(raw_ostream &OS) {
            OS << "Taint Tag:\n";
            OS << "ID: " << static_cast<const void *>(this) << "\n";
            OS << "Value:\n";
            if (this->v){
                this->v->print(OS,true);
            }
            OS << "\nfieldId: " << this->fieldId << " \n";
            OS << "Type: ";
            if (this->type){
                this->type->print(OS);
            }
            OS << "\n";
        }

        void printModInsts(raw_ostream &OS) {
            OS << "###Mod Instruction List###\n";
            for (auto e : this->mod_insts) {
                //Print the mod inst itself.
                OS << "------------INST------------\n";
                InstructionUtils::printInst(e.first, OS);
                //Print the context if any.
                for (auto ctx : e.second) {
                    OS << "------------CTX------------\n";
                    //"ctx" is of type "std::vector<Instruction*>*".
                    for (auto ctx_inst : *ctx) {
                        InstructionUtils::printInst(ctx_inst, OS);
                    }
                }
            }
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
        void dumpInfo(raw_ostream &OS, std::set<TaintTag*> *uniqTags) {

            //OS << "Taint Flag for:";
            //this->targetInstr->print(OS);
            //OS << ", Tainted=" << this->isTainted() << "\n";
            OS << " Instruction Trace: [\n";
            for(std::vector<Instruction *>::iterator SI = this->instructionTrace.begin(); SI != this->instructionTrace.end(); ++SI) {
                OS << (InstructionUtils::getInstructionName((*SI)));
                DILocation *instrLoc = InstructionUtils::getCorrectInstrLocation(*SI);
                OS << " ,lineno: ";
                if (instrLoc != nullptr) {
                    OS << instrLoc->getLine() << " ,file: ";
                    OS << InstructionUtils::escapeJsonString(instrLoc->getFilename());
                } else {
                    OS << "-1";
                }
                OS << "\n";
            }
            OS << "]\n";
            //hz: dump tag information if any.
            if (this->tag) {
                //TODO: is it enough to depend on the pointer value to filter out duplications?
                if (uniqTags && uniqTags->find(this->tag) == uniqTags->end()) {
                    uniqTags->insert(this->tag);
                }
                this->tag->dumpInfo(OS);
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
