//
// Created by machiry on 8/23/16.
//

#ifndef PROJECT_TAINTFLAG_H
#define PROJECT_TAINTFLAG_H

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

using namespace llvm;
namespace DRCHECKER {

//#define DEBUG_INSERT_MOD_INST

    //hz: Class that intends to identify a unique taint source.
    class TaintTag {
    public:
        long fieldId;
        Value *v;
        Type *type;
        //Record all instructions (w/ its call context) that can possibly modify this taint source.
        std::map< Instruction *, std::set<std::vector<Instruction*>*> > mod_insts;
        //If this is a local taint tag (i.e. for user provided arg), record all its comparison constants here.
        std::map< Instruction *, std::set<int64_t>> cmp_constants;
        bool is_global;
        //The AliasObject that is related to this tag.
        void *priv;

        TaintTag(long fieldId, Value *v, bool is_global = true, void *p = nullptr) {
            this -> fieldId = fieldId;
            this -> v = v;
            this -> type = this->getTy();
            this -> is_global = is_global;
            this -> priv = p;
        }

        TaintTag(TaintTag *srcTag) {
            this -> fieldId = srcTag -> fieldId;
            this -> v = srcTag -> v;
            this -> type = srcTag -> type;
            //This is content copy.
            this -> mod_insts = srcTag -> mod_insts;
            this -> cmp_constants = srcTag -> cmp_constants;
            this -> is_global = srcTag -> is_global;
            this -> priv = srcTag -> priv;
        }

        void addCmpConstants(Instruction *inst, int64_t n) {
            if (!inst) {
                return;
            }
            this->cmp_constants[inst].insert(n);
        }

        bool has_cmp_consts() {
            return (!this->cmp_constants.empty());
        }

        void printCmpConsts(raw_ostream &OS) {
            if (!this->has_cmp_consts()) {
                return;
            }
            OS << "####CMP CONSTS LIST####\n";
            for (auto& e : this->cmp_constants) {
                OS << "--- ";
                InstructionUtils::printInst(e.first, OS);
                //Print the context if any.
                for (auto& x : e.second) {
                    OS << x << ", ";
                }
                OS << "\n";
            }
        }

        std::string getTypeStr() {
            Type *ty = this->getTy();
            if (!ty) {
                return "unknown";
            }
            std::string str;
            llvm::raw_string_ostream ss(str);
            ty->print(ss);
            return ss.str();
        }

        Type *getTy() {
            if (!(this->v)){
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
                   this->v == dstTag->v &&
                   this->type == dstTag->type &&
                   this->is_global == dstTag->is_global;
        }

        /*
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
        */

        //NOTE: we now assume a context can only be created once in AnalysisContext and thus the ptr "call_ctx" is different for different contexts.
        void insertModInst(Instruction *inst, std::vector<Instruction *> *call_ctx) {
            if (!inst || !call_ctx){
#ifdef DEBUG_INSERT_MOD_INST
                dbgs() << "insertModInst: null inst or call_ctx\n";
#endif
                return;
            }
            this->mod_insts[inst].insert(call_ctx);
        }

        bool has_mod_insts() {
            return (!this->mod_insts.empty());
        }

        void dumpInfo(raw_ostream &OS) {
            OS << "Taint Tag: " << static_cast<const void *>(this) << "\n";
            OS << "Type: " << InstructionUtils::getTypeStr(this->type) << " | " << this->fieldId << " is_global: " << this->is_global << "\n";
            OS << "Value: " << InstructionUtils::getValueStr(this->v) << "\n";
        }

        void printModInsts(raw_ostream &OS, std::map<BasicBlock*,std::set<uint64_t>> *switchMap) {
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
                    //Print out extra information about how to reach this instruction from the entry point in this call context.
                    //E.g. what "cmd" value should we use for the entry-point ioctl()?
                    std::set<uint64_t> *p_cmds = InstructionUtils::getCmdValues(ctx,e.first,switchMap);
                    if (!p_cmds) {
                        continue;
                    }
                    OS << "-----EXT-----\n";
                    for (auto cmd : *p_cmds){
                        OS << cmd << ", ";
                    }
                    OS << "\n";
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
            if (srcOperand) {
                Instruction *srcInstr = dyn_cast<Instruction>(srcOperand);
                if(srcInstr != nullptr && lastInstr != srcInstr) {
                    this->instructionTrace.push_back(srcInstr);
                }
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

        void setTag(TaintTag *tag) {
            this -> tag = tag;
        }

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
        void dumpInfo(raw_ostream &OS, std::set<TaintTag*> *uniqTags = nullptr) {

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
            OS << "is_inherent: " << this->is_inherent << "\n";
            //hz: dump tag information if any.
            if (this->tag) {
                //TODO: is it enough to depend on the pointer value to filter out duplications?
                if (uniqTags) {
                    uniqTags->insert(this->tag);
                }
                this->tag->dumpInfo(OS);
            }

        }

        //hz: add taint tag support.
        TaintTag *tag;

        //hz: "inherent" means this TaintFlag is not propagated to a value, instead, it's created together w/ the value, indicating
        //that the value itself is a taint source (i.e. an OutsideObject).
        bool is_inherent = false;

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
