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
        Value *v = nullptr;
        Type *type = nullptr;
        //Record all instructions (w/ its call context) that can possibly modify this taint source.
        std::map< Instruction *, std::set<std::vector<Instruction*>*> > mod_insts;
        //If this is a local taint tag (i.e. for user provided arg), record all its comparison constants here.
        std::map< Instruction *, std::set<int64_t>> cmp_constants;
        bool is_global;
        //The AliasObject that is related to this tag.
        void *priv = nullptr;

        TaintTag(long fieldId, Value *v, bool is_global = true, void *p = nullptr) {
            this -> fieldId = fieldId;
            this -> v = v;
            this -> type = this->getTy();
            this -> is_global = is_global;
            this -> priv = p;
        }

        //In case we don't have an actual llvm "Value" pointing to the object, we can just provide the obj type.
        TaintTag(long fieldId, Type *ty, bool is_global = true, void *p = nullptr) {
            this -> fieldId = fieldId;
            this -> v = nullptr;
            this -> type = ty;
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
            if (!this->type) {
                this->type = this->getTy();
            }
            return InstructionUtils::getTypeStr(this->type);
            /*
            std::string str;
            llvm::raw_string_ostream ss(str);
            this->type->print(ss);
            return ss.str();
            */
        }

        Type *getTy() {
            if (this->type) {
                return this->type;
            }
            if (!(this->v)){
                return nullptr;
            }
            Type *ty = this->v->getType();
            if (ty->isPointerTy()){
                ty = ty->getPointerElementType();
            }
            /*
            if (dyn_cast<CompositeType>(ty) && InstructionUtils::isIndexValid(ty,fieldId)) {
                return dyn_cast<CompositeType>(ty)->getTypeAtIndex(fieldId);
            }
            */
            return ty;
        }

        Type *getFieldTy() {
            Type *hostTy = this->getTy();
            if (!hostTy || !dyn_cast<CompositeType>(hostTy) || !InstructionUtils::isIndexValid(hostTy,this->fieldId)) {
                return nullptr;
            }
            return dyn_cast<CompositeType>(hostTy)->getTypeAtIndex(this->fieldId);
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
                   this->is_global == dstTag->is_global &&
                   this->priv == dstTag->priv;
            /*
            if ( (this->priv == dstTag->priv && this->fieldId == dstTag->fieldId) ||
                 (dyn_cast<CompositeType>(this->type) && InstructionUtils::same_types(this->type,dstTag->type) && this->fieldId == dstTag->fieldId && this->is_global == dstTag->is_global)
               ){
                return true;
            }
            return false;
            */
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
            OS << "Taint Tag: " << (const void *)this << "\n";
            OS << "Type: " << InstructionUtils::getTypeStr(this->type) << " | " << this->fieldId << " is_global: " << this->is_global << "\n";
            OS << "Obj: " << (const void*)this->priv << " Value: " << InstructionUtils::getValueStr(this->v) << "\n";
        }

        void dumpInfo_light(raw_ostream &OS) {
            OS << "Tag: " << (const void *)this;
            OS << " Type: " << InstructionUtils::getTypeName(this->type) << " | " << this->fieldId << " is_global: " << this->is_global << " obj: " << (const void*)this->priv << "\n";
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
        TaintFlag(InstLoc *targetInstr, bool is_tainted, TaintTag *tag = nullptr) {
            assert(targetInstr != nullptr && "Target Instruction cannot be NULL");
            this->targetInstr = targetInstr;
            this->instructionTrace.push_back(targetInstr);
            this->is_tainted = is_tainted;
            this->tag = tag;
        }

        TaintFlag(TaintFlag *copyTaint, InstLoc *targetInstr, InstLoc *srcOperand) {
            this->targetInstr = targetInstr;
            this->is_tainted = copyTaint->isTainted();
            // copy the instruction trace from the source taint guy
            this->instructionTrace.insert(instructionTrace.begin(),
                                          copyTaint->instructionTrace.begin(), copyTaint->instructionTrace.end());
            // add the source instruction into the trace.
            this->addInstructionToTrace(srcOperand);
            // add target inst to the trace.
            this->addInstructionToTrace(targetInstr);
            //hz: tag propagation.
            this->tag = copyTaint->tag;
        }

        //hz: A copy w/ a different tag.
        TaintFlag(TaintFlag *copyTaint, TaintTag *tag) {
            this->targetInstr = copyTaint->targetInstr;
            this->is_tainted = copyTaint->isTainted();
            // copy the instruction trace from the source taint guy
            this->instructionTrace.insert(instructionTrace.begin(),
                                          copyTaint->instructionTrace.begin(), copyTaint->instructionTrace.end());
            this->tag = tag;
        }

        TaintFlag(InstLoc *targetInstr) : TaintFlag(targetInstr, false) {}
        //Destructors
        ~TaintFlag() {}

        void setTag(TaintTag *tag) {
            this->tag = tag;
        }

        bool isTainted() const {
            return is_tainted;
        }

        bool isTaintEquals(const TaintFlag *dstTaint) const {
            if(dstTaint != nullptr) {
                //hz: we consider the below three properties:
                //(1) the targetInst of this taintFlag
                //(2) whether it's tainted or not
                //(3) the taint source, which is wrapped in our TaintTag class.
                //These are properties we consider when comparing two taint flags.
                //Property (1)
                if (!this->targetInstr != !dstTaint->targetInstr) {
                    return false;
                }
                if (this->targetInstr && !this->targetInstr->same(dstTaint->targetInstr)) {
                    return false;
                }
                //Property (2)
                if (this->isTainted() != dstTaint->isTainted()){
                    return false;
                }
                //Property (3):
                if (!this->tag != !dstTaint->tag) {
                    return false;
                }
                if (this->tag) {
                    return this->tag->isTagEquals(dstTaint->tag);
                }
                return true;
            }
            return false;
        }

        void addInstructionToTrace(InstLoc *toAdd) {
            if (!toAdd) {
                return;
            }
            if (this->instructionTrace.size() > 0) {
                // check if last instruction is the current instruction.
                InstLoc *lastInstr = this->instructionTrace.back();
                if (toAdd->same(lastInstr)) {
                    return;
                }
            }
            this->instructionTrace.push_back(toAdd);
        }

        InstLoc *targetInstr;
        // trace of instructions that resulted in this taint.
        std::vector<InstLoc*> instructionTrace;
        void dumpInfo(raw_ostream &OS) {
            OS << " Instruction Trace: [\n";
            for (InstLoc *inst : this->instructionTrace) {
                if (inst) {
                    inst->print(OS);
                }
            }
            OS << "]\n";
            OS << "is_inherent: " << this->is_inherent << "\n";
            //hz: dump tag information if any.
            if (this->tag) {
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
