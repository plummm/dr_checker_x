//
// Created by machiry on 12/4/16.
//
#include <CFGUtils.h>
#include "PointsToUtils.h"
#include "GlobalVisitor.h"
#include "../../Utils/include/InstructionUtils.h"

namespace DRCHECKER {

// #define DEBUG_GLOBAL_ANALYSIS
//#define DEBUG_CALL_INSTR
#define DONOT_CARE_COMPLETION
#define MAX_CALLSITE_DEPTH 7
#define MAX_FUNC_PTR 3
#define SMART_FUNCTION_PTR_RESOLVING
// #define DEBUG_BB_VISIT
#define FUNC_BLACKLIST
#define HARD_LOOP_LIMIT
#define MAX_LOOP_CNT 1
#define SKIP_ASAN_INST

    // Basic visitor functions.
    // call the corresponding function in the child callbacks.
    void GlobalVisitor::visitAllocaInst(AllocaInst &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitAllocaInst(I);
        }

    }

    void GlobalVisitor::visitCastInst(CastInst &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitCastInst(I);
        }
    }

    void GlobalVisitor::visitBinaryOperator(BinaryOperator &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitBinaryOperator(I);
        }
    }

    void GlobalVisitor::visitPHINode(PHINode &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitPHINode(I);
        }
    }

    void GlobalVisitor::visitSelectInst(SelectInst &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitSelectInst(I);
        }
    }

    void GlobalVisitor::visitGetElementPtrInst(GetElementPtrInst &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitGetElementPtrInst(I);
        }
    }

    void GlobalVisitor::visitLoadInst(LoadInst &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitLoadInst(I);
        }
    }

    void GlobalVisitor::visitStoreInst(StoreInst &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitStoreInst(I);
        }
    }

    void GlobalVisitor::visitVAArgInst(VAArgInst &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitVAArgInst(I);
        }
    }

    void GlobalVisitor::visitVACopyInst(VACopyInst &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitVACopyInst(I);
        }
    }

    void GlobalVisitor::visitReturnInst(ReturnInst &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitReturnInst(I);
        }
    }

    void GlobalVisitor::visitICmpInst(ICmpInst &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitICmpInst(I);
        }
    }

    void GlobalVisitor::visitBranchInst(BranchInst &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitBranchInst(I);
        }
    }

    //hz: add support for switch inst.
    void GlobalVisitor::visitSwitchInst(SwitchInst &I) {
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visitSwitchInst(I);
        }
    }

    bool checkObjTainted(ObjectPointsTo *pto, int depth){
        if(depth >= 2){
            return false;
        }
        auto target_field = pto->dstfieldId;
        auto dstObj = pto->targetObject;
        if(dstObj){
            auto fdtaintinfo = dstObj->getFieldTaint(target_field);
            if(fdtaintinfo){
                for(auto taintinfo : fdtaintinfo->targetTaint){
                    if(taintinfo->isTainted()){
                        return true;
                    }
                }
            }
            for(auto fdpto : dstObj->pointsTo){
                for(auto pto_o : fdpto.second){
                    if(checkObjTainted(pto_o, depth + 1)){
                        return true;
                    }
                }
            }
        }
        return false;
    }


    void GlobalVisitor::processCalledFunction(CallInst &I, Function *currFunc) {
        std::string currFuncName = currFunc->getName().str();
#ifdef DONOT_CARE_COMPLETION
        //hz: we need to use "2*MAX-1" since for each call site we insert both the call inst and the callee entry inst into the context.
        if(this->currFuncCallSites->size() > 2 * MAX_CALLSITE_DEPTH - 1) {
            //errs() << "MAX CALL SITE DEPTH REACHED, IGNORING:" << currFuncName << "\n";
            return;
        }
#endif

        //A hacking: set up a blacklist for certain time-consuming functions..


        if(this->currState.taintedAllTarget){

#ifdef FUNC_BLACKLIST
            //std::set<std::string> black_funcs{"con_write","do_con_write","io_serial_out","io_serial_in","emulation_required", "kfree", "mutex_lock", "mutex_unlock", "queue_delayed_work_on", "pvclock_read_wallclock", "record_times", "update_rq_clock", "sched_clock_idle_sleep_event", \
                "printk", "vprintk", "queued_spin_lock_slowpath", "__pv_queued_spin_lock_slowpath", "queued_read_lock_slowpath", "queued_write_lock_slowpath", "dump_page", "__warn_printk", "__put_page", "refcount_dec_and_test", "___cache_free", "trace_kmem_cache_free", "kfree_skb", "refcount_sub_and_test", "unix_write_space", \
                "free_percpu","refcount_sub_and_test_checked","refcount_dec_and_test_checked","refcount_dec_and_mutex_lock","_raw_spin_lock_bh", "trace_lock_acquire", "_raw_spin_unlock_bh", "lock_release", "mutex_lock_nested", "__mutex_lock", "__mutex_lock_common", "__might_sleep", "llvm.lifetime.start.p0i8", "___might_sleep", "print_kernel_ident", "rcu_is_watching", "debug_lockdep_rcu_enabled"};
            std::set<std::string> black_funcs{"__kasan_check_read", "__kasan_check_write","kasan_report_double_free", "kasan_check_read", "kasan_check_write", "kasan_unpoison_shadow", "queue_delayed_work_on", "pvclock_read_wallclock","mutex_lock", "__mutex_lock", "mutex_unlock", "__mutex_unlock", "record_times", "kfree", "update_rq_clock", "sched_clock_idle_sleep_event", \
            "__warn_printk", "srm_printk", "snd_printk", "dbgp_printk", "ql4_printk", "printk", "vprintk", "__dump_page", "irq_stack_union", "queued_spin_lock_slowpath", "__pv_queued_spin_lock_slowpath", "queued_read_lock_slowpath", "queued_write_lock_slowpath"};
            std::set<std::string> black_funcs_inc{"asan_report","llvm.dbg","__sanitizer_cov_trace_pc"};
            if (black_funcs.find(currFuncName) != black_funcs.end()) {
                dbgs() << "Func in blacklist, IGNORING:" << currFuncName << "\n";
                return;
            }
            if(this->currState.taintedindirectcalls.find(&I) != this->currState.taintedindirectcalls.end()){
                return;
            }

            for (auto& x : black_funcs_inc) {
                if (currFuncName.find(x) != std::string::npos) {
                    return;
                }
            }
#endif




            int argnum = I.getNumArgOperands();
            for(int i = 0; i < argnum; i++){
                auto arg = I.getArgOperand(i);
                if(!hasPointsToObjects(arg)){
                    arg = arg->stripPointerCasts();
                }
                auto ptos = getPointsToObjects(arg);
                if(ptos){
                    for(auto pto : *ptos){
                        /*long target_field = pto->dstfieldId;
                        auto dstObj = pto->targetObject;
                        auto fdtaintinfo = dstObj->getFieldTaint(target_field);
                        if(fdtaintinfo){
                            for(auto taintinfo : fdtaintinfo->targetTaint){
                                if(taintinfo->isTainted()){
                                    goto UsefulCall;
                                }
                            }
                        }*/
                        if(checkObjTainted(pto, 0)){
                            goto UsefulCall;
                        }
                    }
                }
            }
            return;
        }

        

        UsefulCall:


        


        // Create new context.
        //Set up arguments of the called function.
        std::vector<Instruction*> *newCallContext = new std::vector<Instruction *>();
        newCallContext->insert(newCallContext->end(), this->currFuncCallSites->begin(), this->currFuncCallSites->end());
        // create context.
        newCallContext->insert(newCallContext->end(), &I);
        //hz: If this is an indirect call inst, there can be multiple possible target callees, in this situation
        //if we only insert the call inst itself into the "call context", we will not be able to differentiate
        //these target callees... So now for each call inst, we insert both the call inst and the entry inst of the
        //target function into the "call context".
        if (!currFunc->isDeclaration()) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "GlobalVisitor::processCalledFunction: prepare context for: " << currFuncName << " (w/ definition)\n";
#endif
            BasicBlock &bb = currFunc->getEntryBlock();
            newCallContext->insert(newCallContext->end(), bb.getFirstNonPHIOrDbg());
        }else{
            //Insert the call inst again in order to match the 2*MAX-1...
#ifdef DEBUG_CALL_INSTR
            dbgs() << "GlobalVisitor::processCalledFunction: prepare context for: " << currFuncName << " (w/o definition)\n";
#endif
            newCallContext->insert(newCallContext->end(), &I);
        }
        this->currState.getOrCreateContext(newCallContext);

        // new callbacks that handles the current function.
        std::vector<VisitorCallback*> newCallBacks;

        // map of the parent visitor to corresponding child visitor.
        std::map<VisitorCallback*, VisitorCallback*> parentChildCallBacks;

        for (VisitorCallback *currCallback : allCallbacks) {
            VisitorCallback *newCallBack = currCallback->visitCallInst(I, currFunc, this->currFuncCallSites, newCallContext);
            if(newCallBack != nullptr) {
                newCallBacks.insert(newCallBacks.end(), newCallBack);
                parentChildCallBacks[currCallback] = newCallBack;
            }
        }
        // if there are new call backs? then create a GlobalVisitor and run the corresponding  visitor
        if (newCallBacks.size() > 0) {
            // Make sure we have the function definition.
            assert(!currFunc->isDeclaration());
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Analyzing new function: " << currFuncName << " Call depth: " << newCallContext->size() << "\n";
#endif
            //log the current calling context.
            //dbgs() << "CTX: ";
            //InstructionUtils::printCallingCtx(dbgs(),newCallContext,true);
#ifdef TIMING
            dbgs() << "[TIMING] Start func(" << newCallContext->size() << ") " << currFuncName << ": ";
            auto t0 = InstructionUtils::getCurTime(&dbgs());
#endif
            std::vector<std::vector<BasicBlock *> *> *traversalOrder = BBTraversalHelper::getSCCTraversalOrder(*currFunc);
            // Create a GlobalVisitor
            GlobalVisitor *vis = new GlobalVisitor(currState, currFunc, newCallContext, traversalOrder, newCallBacks);
            // Start analyzing the function.
            
            vis->analyze();
            //errs() << "caller: " <<I.getFunction()->getName().str() << " Analyze: "<< currFunc->getName().str() << "\n";
            if (!terminatingFunc) {
                for (int i = 0; i < this->currState.callsiteinfos.size() -1; i++) {
                    auto callee = this->currState.callsiteinfos[i];
                    auto caller = this->currState.callsiteinfos[i+1];
                    errs() << "caller func: " <<caller->funcname << " callee func: "<< callee->funcname << "\n";
                    if (callee->funcname == currFunc->getName().str() && caller->funcname == I.getFunction()->getName().str())
                        terminatingFunc = true;
                }
                if (terminatingFunc) {
                    int argnum = I.getNumArgOperands();
                    bool hasTaintInfo = false;
                    for(int i = 0; i < argnum; i++){
                        auto arg = I.getArgOperand(i);
                        if(!hasPointsToObjects(arg)){
                            arg = arg->stripPointerCasts();
                        }
                        auto ptos = getPointsToObjects(arg);
                        if(ptos){
                            for(auto pto : *ptos){
                                if(checkObjTainted(pto, 0)){
                                    hasTaintInfo = true;
                                }
                            }
                            
                        }
                    }
                    auto ptos = getPointsToObjects(&I);
                    if(ptos){
                        for(auto pto : *ptos){
                            if(checkObjTainted(pto, 0)){
                                hasTaintInfo = true;
                            }
                        }
                    }
                    if(!hasTaintInfo){
                        ofstream fout(this->currState.printPathDir + "/TerminatingFunc");
                        fout << currFunc->getName().str();
                        fout.close();
                    }
                }
            }
            // stitch back the contexts of all the member visitor callbacks.
            for(std::map<VisitorCallback *, VisitorCallback *>::iterator iter = parentChildCallBacks.begin();
                iter != parentChildCallBacks.end();
                ++iter)
            {
                VisitorCallback *parentCallback = iter->first;
                VisitorCallback *childCallback = iter->second;
                parentCallback->stitchChildContext(I, childCallback);
                delete(childCallback);
            }
            delete(vis);
#ifdef TIMING
            dbgs() << "[TIMING] End func(" << newCallContext->size() << ") " << currFuncName << " in: ";
            InstructionUtils::getTimeDuration(t0,&dbgs());
#endif
            //log the current calling context.
            //dbgs() << "CTX: ";
            //InstructionUtils::printCallingCtx(dbgs(),this->currFuncCallSites,true);
        }

        // if(I.getNumArgOperands() > 1){
        //     auto checkptr = I.getArgOperand(1);
        //     auto currtoptaintinfo = this->currState.taintInformation[this->currState.getContext(this->currFuncCallSites)];
        //         if(currtoptaintinfo){
        //             errs() << "found currtoptaintinfo\n" << "\n";
        //             if(currtoptaintinfo->find(checkptr) != currtoptaintinfo->end()){
        //                 errs() << "found srcopr taint info\n";
        //                 for(auto ttinfo : *(*currtoptaintinfo)[checkptr]){
        //                     if(ttinfo->isTainted()){
        //                         errs() << "tainted!\n" << "\n";
        //                     }
        //                 }
        //             }
        //         }
        // }
    }

    // Visit Call Instruction.
    void GlobalVisitor::visitCallInst(CallInst &I) {
        if (this->inside_loop) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Function inside loop, will be analyzed at last iteration\n";
#endif
            return;
        }
        Function *currFunc = I.getCalledFunction();
        if (currFunc == nullptr) {
            // this is to handle casts.
            currFunc = dyn_cast<Function>(I.getCalledValue()->stripPointerCasts());
        }
        // ignore only if the current function is an external function
        if (currFunc == nullptr || !currFunc->isDeclaration()) {
            // check if the call instruction is already processed?
            if (this->visitedCallSites.find(&I) != this->visitedCallSites.end()) {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "Function already processed: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
                return;
            }
            //Only the odd entry in the calling context represents a call site, the even entry is the first inst of a callee.
            for (int i = 1; i < this->currFuncCallSites->size(); i += 2) {
                if ((*this->currFuncCallSites)[i] == &I) {
#ifdef DEBUG_CALL_INSTR
                    dbgs() << "Call-graph cycle found: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
                    return;
                }
            }
        }
        // insert into visited call sites.
        this->visitedCallSites.insert(this->visitedCallSites.end(), &I);

        if(currFunc != nullptr) {
            //errs() << "meet func: " << currFunc->getName().str() << " at callsite linenum: " << I.getDebugLoc().getLine() << "\n";
            if(!this->currState.taintedAllTarget){
                if(this->currState.calltracepointer > 0){
                    auto dbginfo = I.getDebugLoc();
                    auto callsiteline = this->currState.callsiteinfos[this->currState.calltracepointer]->linenum;
                    auto nextfunc = this->currState.callsiteinfos[this->currState.calltracepointer - 1];
                    if(dbginfo && dbginfo.getLine() == callsiteline && currFunc == nextfunc->func){
                            this->currState.calltracepointer--;
                            this->processCalledFunction(I, currFunc);
                        }
                
                }else{
                    if(this->currState.topcallsites.find(&I) != this->currState.topcallsites.end()){
                        this->processCalledFunction(I, currFunc);
                    }
                }
            }else{
                this->processCalledFunction(I, currFunc);
            }
            
            
        } else {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Visiting Indirect call instruction: " << InstructionUtils::getValueStr(&I) << "\n";
#endif
            // if this is inline assembly, ignore the call instruction.
            if(I.isInlineAsm()) {
                return;
            }
            Value *calledValue = I.getCalledValue();
            // get points to information of calledValue and look for only functions.
            std::set<Function*> targetFunctions;
            targetFunctions.clear();
            bool hasTargets = PointsToUtils::getTargetFunctions(this->currState, this->currFuncCallSites,
                                                                calledValue, targetFunctions);
#ifdef SMART_FUNCTION_PTR_RESOLVING
            if (!hasTargets) {
                //NOTE: the below inference is actually a backup method to the "getPossibleMemeberFunction" when
                //we fetch the field pto from an object, so if we are sure that the aforementioned inference
                //has already been performed (and we still get nothing), then no need to do the inference again here.
                Value *v = InstructionUtils::stripAllCasts(calledValue,false);
                if (v && dyn_cast<LoadInst>(v)) {
                    //We must have already tried the inference when processing the "load", so give up now.
                    dbgs() << "We have done the inference previously when processing the load, but still no results...\n";
                    goto out;
                }
                hasTargets = InstructionUtils::getPossibleFunctionTargets(I, targetFunctions);
#ifdef DEBUG_CALL_INSTR
                dbgs() << "Function Pointer targets: " << targetFunctions.size() << "\n";
#endif
                if (targetFunctions.size() > MAX_FUNC_PTR) {
#ifdef DEBUG_CALL_INSTR
                    dbgs() << "Too many Target Functions, give up some, our limit is: " << MAX_FUNC_PTR << "\n";
#endif
                    std::set<Function*> tset = targetFunctions;
                    targetFunctions.clear();
                    int cnt = 0;
                    for (Function *f : tset) {
                        if (cnt >= MAX_FUNC_PTR) {
                            break;
                        }
                        if (f) {
                            targetFunctions.insert(f);
                            ++cnt;
                        }
                    }
                }
            }
#endif
out:
            // get potential target function from a given pointer.
            if(hasTargets) {
                assert(targetFunctions.size() > 0);
#ifdef DEBUG_CALL_INSTR
                dbgs() << "There are: " << targetFunctions.size() << " Target Functions.\n";
#endif
                for(Function *currFunction : targetFunctions) {
                    errs() << "Target func:" << currFunction->getName() << "\n";
                    if(!this->currState.taintedAllTarget){
                        if(this->currState.calltracepointer > 0){
                            auto dbginfo = I.getDebugLoc();
                            auto callsiteline = this->currState.callsiteinfos[this->currState.calltracepointer]->linenum;
                            auto nextfunc = this->currState.callsiteinfos[this->currState.calltracepointer - 1];
                            //errs() << "next func should be: " << nextfunc->funcname << ":" << callsiteline << "\n";
                            if(dbginfo && dbginfo.getLine() == callsiteline && currFunction == nextfunc->func){
                                this->currState.calltracepointer--;
                                this->processCalledFunction(I, currFunction);
                            }
                                
                        }else{
                            if(this->currState.topcallsites.find(&I) != this->currState.topcallsites.end()){
                                this->processCalledFunction(I, currFunction);
                            }
                        }
                    }else{
                        this->processCalledFunction(I, currFunction);
                    }
                }

            } else {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "Function pointer does not point to any functions: " << InstructionUtils::getValueStr(calledValue) 
                << ", So Ignoring\n";
#endif
            }
        }
    }

    void checkObjPtoSize(Value *v, GlobalState * currState, std::vector<Instruction*> *pcallSites){
        auto ptomap = currState->getPointsToInfo(pcallSites);
        if(ptomap->find(v) != ptomap->end()){
            errs() << "size: " << (*ptomap)[v]->size() << "\n";
        }else{
            errs() << "No ptomap\n";
        }
    }

    void createObj4value(Value *v, Instruction* I, GlobalState * currState, std::vector<Instruction*> *pcallSites, int offset){
            if(!v || isa<GlobalVariable>(v)){
                return;
            }
            InstLoc* loc = nullptr;
            if(I){
                loc = new InstLoc(I, pcallSites);
            }
            
            auto ptomap = currState->getPointsToInfo(pcallSites);
            if(ptomap->find(v) == ptomap->end() || (*ptomap)[v]->size() == 0 ){
                OutsideObject *robj = DRCHECKER::createOutsideObj(v,loc);
                if(robj != nullptr){
                    std::set<PointerPointsTo*> ptos;
                    PointerPointsTo *pto = new PointerPointsTo(v,robj,0,loc);
                    ptos.insert(pto);
                    if(ptomap->find(v) == ptomap->end()){
                        (*ptomap)[v] = new std::set<PointerPointsTo*>();
                    }
                    for(auto curpto : ptos){
                        (*ptomap)[v]->insert((*ptomap)[v]->end(), curpto);
                    }
                    
                }
            }
            for(auto ptinfo : *(*ptomap)[v]){       
                    ptinfo->targetObject->setAsTaintFieldSrc(loc, currState->targetDataLayout, true, offset);      
            }

            // OutsideObject *robj = DRCHECKER::createOutsideObj(v,loc);
            // if(robj != nullptr){
            //     std::set<PointerPointsTo*> ptos;
            //     PointerPointsTo *pto = new PointerPointsTo(v,robj,0,loc);
            //     ptos.insert(pto);
            //     std::map<Value*, std::set<PointerPointsTo*>*> *targetPointsToMap = currState->getPointsToInfo(pcallSites);
            //     if (targetPointsToMap->find(v) == targetPointsToMap->end()) {
            //         (*targetPointsToMap)[v] = new std::set<PointerPointsTo*>();
            //     }
            //     std::set<PointerPointsTo*>* existingPointsTo = (*targetPointsToMap)[v];
            //     dbgs() << "Before update, ptos size: " << existingPointsTo->size() <<"\n";
            //     for(PointerPointsTo *currPointsTo : ptos){
            //         existingPointsTo->insert(existingPointsTo->end(), currPointsTo);
            //     }
            //     dbgs() << "After update, ptos size: " << existingPointsTo->size() << "\n";
            //     robj->setAsTaintFieldSrc(loc, dl, true, 0);
                
            //     //TaintFlag tfg(loc);
            //     //robj->taintAllFields(&tfg);
            //     // dbgs() << "sizeof struct obj is "  << robj->targetType->getStructNumElements() << "\n";
            //     // for(long i = 0; i < robj->targetType->getStructNumElements(); i++){
            //     //     robj->addFieldTaintFlag(i, &tfg);
            //     // }
            // }
            return;
        }

    void GlobalVisitor::visit(BasicBlock *BB) {
        if(this->currState.numTimeAnalyzed.find(BB) != this->currState.numTimeAnalyzed.end()) {
#ifdef FAST_HEURISTIC
            if(this->currState.numTimeAnalyzed[BB] >= GlobalVisitor::MAX_NUM_TO_VISIT) {
#ifdef DEBUG_BB_VISIT
                dbgs() << "Ignoring BB:" << BB->getName().str()
                       << " ad it has been analyzed more than:"
                       << GlobalVisitor::MAX_NUM_TO_VISIT << " times\n";
#endif
                return;
            }
#endif
            this->currState.numTimeAnalyzed[BB] = this->currState.numTimeAnalyzed[BB] + 1;
        } else {
            this->currState.numTimeAnalyzed[BB] = 1;
        }
#ifdef DEBUG_BB_VISIT
        dbgs() << "Starting to analyze BB:" <<  BB->getName().str() << ":at:"<< BB->getParent()->getName() << "\n";
        /*
        dbgs() << "<<<<\n";
        BB->print(dbgs());
        dbgs() << ">>>>\n";
        */
#endif
        for(VisitorCallback *currCallback:allCallbacks) {
            currCallback->visit(BB);
        }
#ifdef SKIP_ASAN_INST
        for (Instruction &inst : *BB) {
            if (InstructionUtils::isAsanInst(&inst)) {
                dbgs() << "GlobalVisitor::visit(): Skip ASAN inst: " << InstructionUtils::getValueStr(&inst) << "\n";
                continue;
            }



            // if(this->currState.baseptrmap.find(&inst) != this->currState.baseptrmap.end()){
            //     for(auto v : this->currState.baseptrmap[&inst]){
            //         checkObjPtoSize(v, &this->currState, this->currFuncCallSites);
            //     }
            //     // this->currState.baseptrmap.erase(&inst);
            // }

            if(this->currState.baseptrmap.find(&inst) != this->currState.baseptrmap.end()){
                for(auto v : this->currState.baseptrmap[&inst]){
                    createObj4value(v, &inst, &this->currState, this->currFuncCallSites, this->currState.offset4baseptrs[v]);
                }
                this->currState.baseptrmap.erase(&inst);
                if(this->currState.baseptrmap.size() == 0){
                    this->currState.taintedAllTarget = true;
                    for(auto callsite : *this->currFuncCallSites){
                        this->currState.vulsitecontext.push_back(callsite);
                    }
                    this->currState.vulsitecontext.push_back(&inst);
                    errs() << "All Target baseptrs tainted!" << "\n";
                }
            }

            // errs() << "visiting inst: \n";
            // inst.print(errs());
            // errs() << "\n";
            
            _super->visit(inst);

            // if(this->currState.baseptrmap.find(&inst) != this->currState.baseptrmap.end()){
            //     for(auto v : this->currState.baseptrmap[&inst]){
            //         checkObjPtoSize(v, &this->currState, this->currFuncCallSites);
            //     }
            //     this->currState.baseptrmap.erase(&inst);
            // }
            
        }
#else
        _super->visit(BB->begin(), BB->end());
#endif
    }

    void GlobalVisitor::analyze() {
        // the traversal order should not be null
        assert(this->traversalOrder != nullptr);
        for (unsigned int i = 0; i < this->traversalOrder->size(); i++) {
            // current strongly connected component.
            std::vector<BasicBlock*> *currSCC = (*(this->traversalOrder))[i];
            if (currSCC->size() == 1) {
                BasicBlock* currBB = (*currSCC)[0];
                if (!this->currState.isDeadBB(this->currFuncCallSites,currBB)) {
                    this->inside_loop = false;
                    for(VisitorCallback *currCallback:allCallbacks) {
                        currCallback->setLoopIndicator(false);
                    }
                    //Analyzing single basic block.
                    this->visit(currBB);
                }else {
                    //Current BB is infeasible
#ifdef DEBUG_GLOBAL_ANALYSIS
                    dbgs() << "GlobalVisitor::analyze(): skip the BB since it's infeasible: " 
                    << InstructionUtils::getBBStrID(currBB) << "\n"; 
#endif
                }
            }else {
                unsigned long opt_num_to_analyze = BBTraversalHelper::getNumTimesToAnalyze(currSCC);
#ifdef HARD_LOOP_LIMIT
                if (MAX_LOOP_CNT < opt_num_to_analyze) {
                    opt_num_to_analyze = MAX_LOOP_CNT;
                }
#endif
#ifdef DEBUG_GLOBAL_ANALYSIS
                dbgs() << "Analyzing Loop BBS for:" << opt_num_to_analyze << " number of times\n";
#endif
                this->inside_loop = true;
                for (VisitorCallback *currCallback:allCallbacks) {
                    currCallback->setLoopIndicator(true);
                }
                for (unsigned int l=0; l < opt_num_to_analyze; l++) {
                    // ensure that loop has been analyzed minimum number of times.
                    if(l >= (opt_num_to_analyze-1)) {
                        this->inside_loop = false;
                        for(VisitorCallback *currCallback:allCallbacks) {
                            currCallback->setLoopIndicator(false);
                        }
                    }
                    for (unsigned int j = 0; j < currSCC->size(); j++) {
                        BasicBlock *currBB = (*currSCC)[j];
                        if (!this->currState.isDeadBB(this->currFuncCallSites,currBB)) {
                            this->visit(currBB);
                        }else {
#ifdef DEBUG_GLOBAL_ANALYSIS
                            dbgs() << "GlobalVisitor::analyze(): skip the BB (in a loop) since it's infeasible: " 
                            << InstructionUtils::getBBStrID(currBB) << "\n"; 
#endif
                        }
                    }
                }
#ifdef DEBUG_GLOBAL_ANALYSIS
                dbgs() << "Analyzing Loop BBS END\n";
#endif
                //Analyzing loop.
            }
        }
    }

    std::set<PointerPointsTo*>* GlobalVisitor::getPointsToObjects(Value *srcPointer) {
        // Get points to objects set of the srcPointer at the entry of the instruction
        // currInstruction.
        // Note that this is at the entry of the instruction. i.e INFLOW.
        std::map<Value *, std::set<PointerPointsTo*>*>* targetPointsToMap = this->currState.getPointsToInfo(this->currFuncCallSites);
        // Here srcPointer should be present in points to map.
        if(targetPointsToMap->find(srcPointer) != targetPointsToMap->end()) {
            return (*targetPointsToMap)[srcPointer];
        }
        return nullptr;
    }


    bool GlobalVisitor::hasPointsToObjects(Value *srcPointer) {
        /***
         * Check if the srcPointer has any pointto objects at currInstruction
         */
        std::map<Value*, std::set<PointerPointsTo*>*> *targetPointsToMap = this->currState.getPointsToInfo(this->currFuncCallSites);
        return targetPointsToMap != nullptr &&
               targetPointsToMap->find(srcPointer) != targetPointsToMap->end() &&
               (*targetPointsToMap)[srcPointer] &&
               (*targetPointsToMap)[srcPointer]->size();
    }


}

