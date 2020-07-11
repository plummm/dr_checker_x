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
#include "../../Utils/include/CFGUtils.h"
#include <vector>

#define DEBUG_UPDATE_FIELD_TAINT

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

        void dumpInfo_light(raw_ostream &OS, bool lbreak = true) {
            OS << "TAG(" << (const void *)this << "):" << InstructionUtils::getTypeName(this->type) << "|" << this->fieldId << "(OBJ:" << (const void*)this->priv << ",G:" << this->is_global << ")";
            if (lbreak) {
                OS << "\n";
            }
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
        TaintFlag(InstLoc *targetInstr, bool is_tainted = true, TaintTag *tag = nullptr, bool is_weak = false) {
            assert(targetInstr != nullptr && "Target Instruction cannot be NULL");
            this->targetInstr = targetInstr;
            this->instructionTrace.push_back(targetInstr);
            this->is_tainted = is_tainted;
            this->tag = tag;
            this->is_weak = is_weak;
            this->is_active = true;
        }

        TaintFlag(TaintFlag *copyTaint, InstLoc *targetInstr) {
            this->targetInstr = targetInstr;
            this->is_tainted = copyTaint->isTainted();
            // copy the instruction trace from the source taint guy
            this->instructionTrace.insert(instructionTrace.begin(),
                                          copyTaint->instructionTrace.begin(), copyTaint->instructionTrace.end());
            // add target inst to the trace.
            this->addInstructionToTrace(targetInstr);
            //hz: tag propagation.
            this->tag = copyTaint->tag;
            this->is_weak = copyTaint->is_weak;
            this->is_active = copyTaint->is_active;
        }

        //hz: A copy w/ a different tag.
        TaintFlag(TaintFlag *copyTaint, TaintTag *tag) {
            this->targetInstr = copyTaint->targetInstr;
            this->is_tainted = copyTaint->isTainted();
            // copy the instruction trace from the source taint guy
            this->instructionTrace.insert(instructionTrace.begin(),
                                          copyTaint->instructionTrace.begin(), copyTaint->instructionTrace.end());
            this->tag = tag;
            this->is_weak = copyTaint->is_weak;
            this->is_active = copyTaint->is_active;
        }

        //Destructors
        ~TaintFlag() {}

        void setTag(TaintTag *tag) {
            this->tag = tag;
        }

        bool isTainted() const {
            return is_tainted;
        }

        //NOTE: we don't consider the "is_weak" and "is_active" properties in the comparison now.
        bool isTaintEquals(const TaintFlag *dstTaint) const {
            if(dstTaint != nullptr) {
                //hz: we consider the below three properties:
                //(1) the targetInst of this taintFlag
                //(2) whether it's tainted or not
                //(3) the taint source, which is wrapped in our TaintTag class.
                //(4) the taint path/trace
                //These are properties we consider when comparing two taint flags.
                //Property (1)
                if (!this->targetInstr != !dstTaint->targetInstr) {
                    return false;
                }
                if (this->targetInstr && !this->targetInstr->same(dstTaint->targetInstr)) {
                    return false;
                }
                //Property (2)
                if (this->isTainted() != dstTaint->isTainted()) {
                    return false;
                }
                //Property (3):
                if (!this->tag != !dstTaint->tag) {
                    return false;
                }
                if (this->tag && !this->tag->isTagEquals(dstTaint->tag)) {
                    return false;
                }
                //Property (4):
                if (this->instructionTrace.size() != dstTaint->instructionTrace.size()) {
                    return false;
                }
                for (int i = 0; i < this->instructionTrace.size(); ++i) {
                    if (!this->instructionTrace[i] != !dstTaint->instructionTrace[i]) {
                        return false;
                    }
                    if (this->instructionTrace[i] && !(this->instructionTrace[i])->same(dstTaint->instructionTrace[i])) {
                        return false;
                    }
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

        //Decide whether this TF can be propagated to a target inst location, used to validate a taint path.
        //This is just a wrapper for convenience.
        bool canReach(InstLoc *dest) {
            if (!dest) {
                return false;
            }
            return dest->reachable(this->targetInstr);
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
            OS << "is_inherent: " << this->is_inherent << " is_active: " << this->is_active << " is_weak: " << this->is_weak << "\n";
            //hz: dump tag information if any.
            if (this->tag) {
                this->tag->dumpInfo(OS);
            }

        }

        //Output a compact info line of this TF, omitting the trace.
        void dumpInfo_light(raw_ostream &OS, bool lbreak = true) {
            //Print the tag info.
            if (this->tag) {
                this->tag->dumpInfo_light(OS,false);
            }else {
                OS << "NULL";
            }
            OS << " @ ";
            //Print the target inst.
            if (this->targetInstr) {
                this->targetInstr->print_light(OS,false);
            }
            //Print states.
            OS << " i/a/w: " << (int)this->is_inherent << "/" << (int)this->is_active << "/" << (int)this->is_weak;
            if (lbreak) {
                OS << "\n";
            }
        }

        //hz: add taint tag support.
        TaintTag *tag;

        //hz: "inherent" means this TaintFlag is not propagated to a value, instead, it's created together w/ the value, indicating
        //that the value itself is a taint source (i.e. an OutsideObject).
        bool is_inherent = false;

        //Indicates whether the flag is currently in effect (e.g. it may be overwritten by another taint).
        bool is_active = true;

        //Indicates whether this is a weak taint flag (i.e. it may or may not taint the target value/field since the "may point-to" results yielded by the pointer analysis).
        bool is_weak = false;

        // flag to indicate the taint flag.
        //NOTE that if this is "false", we treat it as a taint kill (sanitizer)..
        bool is_tainted;
    private:

    };

    /***
     * Class that represents taint of an object field.
     */
    class FieldTaint {
    public:
        long fieldId;
        std::set<TaintFlag*> targetTaint;

        FieldTaint(long srcField) {
            this->fieldId = srcField;
        }

        FieldTaint() {
            this->fieldId = -1;
        }

        ~FieldTaint() {
            //TODO: implement this in a smart way.
            /*for(auto currT:targetTaint) {
                delete(currT);
            }*/
        }

        bool empty() {
            return (this->targetTaint.size() == 0);
        }

        bool hasActiveTaint() {
            for (auto tf : this->targetTaint) {
                if (tf && tf->is_active && tf->is_tainted) {
                    return true;
                }
            }
            return false;
        }

        //Insert a TaintFlag to the existing TF set, there are multiple things we need to consider:
        //(1) duplication
        //(2) whether the new TF will block/mask any old TFs (e.g. post-dominate).
        //This is very similar to the logic of "updateFieldPointsTo" in the Alias Analysis, we also need to rely on memory SSA.
        bool addTf(TaintFlag *ntf) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
            dbgs() << "FieldTaint::addTf(): add TF for field " << this->fieldId << "\n";
#endif
            if (!ntf) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
                dbgs() << "FieldTaint::addTf(): null new TF!\n";
#endif
                return false;
            }
            //Reactivation phase: if the entry function has changed, we need to deactivate the TFs propagated in the previous entry,
            //and then re-activate the inherent TF if present.
            InstLoc *loc = ntf->targetInstr;
            if (loc && loc->hasCtx() && (*loc->ctx)[0]) {
                this->resetTfs((*loc->ctx)[0]);
            }
            //If the to_add is a taint kill but we actually don't have any active taints (i.e. not tainted now), we can just return. 
            if (!ntf->is_tainted && !this->hasActiveTaint()) {
                return false;
            }
            bool is_dup = false;
            std::set<TaintFlag*> to_del;
            for (TaintFlag *tf : this->targetTaint) {
                if (!tf) {
                    continue;
                }
                if (tf->is_active && ntf->is_active && !ntf->is_weak) {
                    //Strong taint, see whether it will kill/override the existing taint.
                    if (loc && loc->postDom(tf->targetInstr)) {
                        to_del.insert(tf);
                    }
                }
                if (is_dup || (tf != ntf && !ntf->isTaintEquals(tf))) {
                    continue;
                }
                //Ok, we already have an exactly same taint flag.
                is_dup = true;
                //TODO: justify the decision to update the "is_weak" to the strongest value...
                if (ntf->is_weak != tf->is_weak) {
                    tf->is_weak = false;
                }
                //Update the active state to the latest.
                tf->is_active = ntf->is_active;
            }
            if (!is_dup) {
                //Insert the new TF.
                this->targetTaint.insert(ntf);
#ifdef DEBUG_UPDATE_FIELD_TAINT
                dbgs() << "FieldTaint::addTf(): +++TF: ";
                ntf->dumpInfo_light(dbgs());
#endif
            }
            //De-activate the overriden TFs, if any.
            for (TaintFlag *tf : to_del) {
                tf->is_active = false;
#ifdef DEBUG_UPDATE_FIELD_TAINT
                dbgs() << "FieldTaint::addTf(): ---TF: ";
                tf->dumpInfo_light(dbgs());
#endif
            }
#ifdef DEBUG_UPDATE_FIELD_TAINT
            dbgs() << "FieldTaint::addTf(): post-stats: ";
            this->logFieldTaint(dbgs());
#endif
            return !is_dup;
        }

        //This function needs to be called (and only called) when we have just finished analyzing an top-level entry function
        //and want to record which non-inherent TFs can last to the end.
        void collectWinnerTfs() {
            //First get the current entry function we are in.
            if (!this->lastReset || !this->lastReset->getParent()) {
                return;
            }
            Function *efunc = this->lastReset->getFunction();
            if (!efunc) {
                return;
            }
            if (this->winnerTfs.find(this->lastReset) != this->winnerTfs.end()) {
                return;
            }
            //Then get all return sites of the entry function.
            std::set<Instruction*> rets;
            BBTraversalHelper::getRetInsts(efunc, rets);
            //Now caculate the winners..
            std::vector<Instruction*> ctx;
            ctx.push_back(this->lastReset);
            for (Instruction *ri : rets) {
                if (!ri) {
                    continue;
                }
                InstLoc rloc(ri,&ctx);
                std::set<TaintFlag*> wtfs;
                this->doGetTf(&rloc,wtfs);
                //Exclude the inherent TFs..
                for (TaintFlag *wtf : wtfs) {
                    if (wtf && !wtf->is_inherent) {
                        this->winnerTfs[this->lastReset].insert(wtf);
                    }
                }
            }
        }

        //Reset the TFs due to the top entry function switch.
        void resetTfs(Instruction *entry) {
            assert(entry);
            if (!this->lastReset) {
                this->lastReset = entry;
            }
            if (this->lastReset == entry) {
                //Still within the same top-level entry func, no need to reset.
                return;
            }
            //Ok, we need to do the reset...
#ifdef DEBUG_UPDATE_FIELD_TAINT
            dbgs() << "FieldTaint::resetTfs(): reset field (" << this->fieldId << ") taint since we have switched to a new entry: ";
            InstructionUtils::printInst(entry,dbgs());
#endif
            //Before the actual reset, let's first record the winner TFs in the previous entry function.
            this->collectWinnerTfs();
            //Do the reset.
            this->lastReset = entry;
            //We need to:
            //(1) deactivate those TFs propagated under different entry functions.
            //(2) reactivate the inherent TFs if any. (it will be strange if we don't have one...)
            for (TaintFlag *tf : this->targetTaint) {
                if (!tf) {
                    continue;
                }
                InstLoc *loc = tf->targetInstr;
                //TODO: whether to treat the TF w/ null targetInstr the same as an inherent TF.
                if (tf->is_inherent || !loc) {
                    tf->is_active = true;
                    continue;
                }
                if (tf->is_active && loc && !loc->sameEntry(entry)) {
                    tf->is_active = false;
                }
            }
            return;
        }

        //Get the TFs that are valid at the "loc" (e.g. some TFs may be overridden by the others).
        //The logic is similar to "fetchFieldPointsTo" in the Alias Analysis.
        bool getTf(InstLoc *loc, std::set<TaintFlag*> &r) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
            dbgs() << "FieldTaint::getTf(): fetch taint for field: " << this->fieldId << "\n";
#endif
            //Reactivation phase: if the entry function has changed, we need to deactivate the TFs propagated in the previous entry,
            //and then re-activate the inherent TF if present.
            if (loc && loc->hasCtx() && (*loc->ctx)[0]) {
                this->resetTfs((*loc->ctx)[0]);
            }
            return this->doGetTf(loc,r);
        }

        //This method simply returns all inherent TFs w/o considering the current "loc" and memory SSA,
        //this can be useful since inherent TFs are special and in some scenarios we may need access them.
        //NOTE: in theory there can be only one inherent TF for each object or field, we use such a "return set" interface just for safe.
        bool getInherentTf(std::set<TaintFlag*> &r) {
            for (TaintFlag *tf : this->targetTaint) {
                if (tf && tf->is_inherent) {
                    r.insert(tf);
                }
            }
            return !!r.size();
        }

        TaintFlag *getInherentTf() {
            for (TaintFlag *tf : this->targetTaint) {
                if (tf && tf->is_inherent) {
                    return tf;
                }
            }
            return nullptr;
        }

        void logFieldTaint(raw_ostream &O, bool lbreak = true) {
            int act = 0, inh = 0, wea = 0, tan = 0;
            for (TaintFlag *tf : this->targetTaint) {
                if (!tf) {
                    continue;
                }
                if (tf->is_tainted) {
                    ++tan;
                }
                if (tf->is_active) {
                    ++act;
                }
                if (tf->is_inherent) {
                    ++inh;
                }
                if (tf->is_weak) {
                    ++wea;
                }
            }
            O << "total/tan/act/inh/weak: " << this->targetTaint.size() << "/" << tan << "/" << act << "/" << inh << "/" << wea;
            if (lbreak) {
                O << "\n";
            }
         }

        private:
        //This is the first inst of the entry function for which we have already swicthed to and done the TF reset.
        Instruction *lastReset = nullptr;

        //"winner" means that a non-inherent field taint TF can last until the top-level entry function returns, 
        //w/o being killed or masked by other TFs, we count on these "winner" TFs to construct reliable single-thread user-taint chain.
        //NOTE that if we want to detect the concurrency bugs, we can extend our scope to those killed/masked TFs on the half way.
        std::map<Instruction*,std::set<TaintFlag*>> winnerTfs;

        bool doGetTf(InstLoc *loc, std::set<TaintFlag*> &r) {
            //First get all active non-kill TFs and blockers.
            std::set<InstLoc*> blocklist;
            std::set<TaintFlag*> actTf;
            for (TaintFlag *tf : this->targetTaint) {
                if (!tf || !tf->is_active) {
                    continue;
                }
                if (tf->is_tainted) {
                    actTf.insert(tf);
                }
                if (tf->targetInstr && !tf->is_weak) {
                    blocklist.insert(tf->targetInstr);
                }
            }
            //Get the live TFs at the "loc"..
            if (loc) {
                for (TaintFlag *tf : actTf) {
                    //NOTE that if "tf->targetInstr" is null, the TF will treated as a pre-set global TF.
                    if (loc->reachable(tf->targetInstr,&blocklist)) {
                        r.insert(tf);
                    }
                    //For logging..
                    if (!tf->targetInstr) {
#ifdef DEBUG_UPDATE_FIELD_TAINT
                        dbgs() << "!!! FieldTaint::getTf(): TF w/o targetInstr: ";
                        tf->dumpInfo_light(dbgs());
#endif
                    }
                }
            }else {
#ifdef DEBUG_UPDATE_FIELD_TAINT
                dbgs() << "FieldTaint::getTf(): null target loc! Return all active TFs: " << actTf.size() << "\n";
#endif
                r.insert(actTf.begin(),actTf.end());
            }
#ifdef DEBUG_UPDATE_FIELD_TAINT
            dbgs() << "FieldTaint::getTf(): final stats: total/act/ret: " << this->targetTaint.size() << "/" << actTf.size() << "/" << r.size() << "\n";
#endif
            return true;
        }
    };

}

#endif //PROJECT_TAINTFLAG_H
