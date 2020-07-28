//
// Created by machiry on 12/4/16.
//
#include <CFGUtils.h>
#include "PointsToUtils.h"
#include "GlobalVisitor.h"
#include "../../Utils/include/InstructionUtils.h"

namespace DRCHECKER {

//#define DEBUG_GLOBAL_ANALYSIS
#define DEBUG_CALL_INSTR
#define DONOT_CARE_COMPLETION
#define MAX_CALLSITE_DEPTH 5
#define MAX_FUNC_PTR 3
#define SMART_FUNCTION_PTR_RESOLVING
#define DEBUG_BB_VISIT
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

    void GlobalVisitor::processCalledFunction(CallInst &I, Function *currFunc) {
        std::string currFuncName = currFunc->getName().str();
#ifdef DONOT_CARE_COMPLETION
        //hz: we need to use "2*MAX-1" since for each call site we insert both the call inst and the callee entry inst into the context.
        if(this->currFuncCallSites->size() > 2 * MAX_CALLSITE_DEPTH - 1) {
            errs() << "MAX CALL SITE DEPTH REACHED, IGNORING:" << currFuncName << "\n";
            return;
        }
#endif

        //A hacking: set up a blacklist for certain time-consuming functions..
#ifdef FUNC_BLACKLIST
        std::set<std::string> black_funcs{"con_write","do_con_write","io_serial_out","io_serial_in","emulation_required"};
        std::set<std::string> black_funcs_inc{"asan_report","llvm.dbg","__sanitizer_cov_trace_pc"};
        if (black_funcs.find(currFuncName) != black_funcs.end()) {
            dbgs() << "Func in blacklist, IGNORING:" << currFuncName << "\n";
            return;
        }
        for (auto& x : black_funcs_inc) {
            if (currFuncName.find(x) != std::string::npos) {
                return;
            }
        }
#endif
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
            dbgs() << "CTX: ";
            InstructionUtils::printCallingCtx(dbgs(),newCallContext,true);
#ifdef TIMING
            dbgs() << "[TIMING] Start func(" << newCallContext->size() << ") " << currFuncName << ": ";
            auto t0 = InstructionUtils::getCurTime(&dbgs());
#endif
            std::vector<std::vector<BasicBlock *> *> *traversalOrder = BBTraversalHelper::getSCCTraversalOrder(*currFunc);
            // Create a GlobalVisitor
            GlobalVisitor *vis = new GlobalVisitor(currState, currFunc, newCallContext, traversalOrder, newCallBacks);
            // Start analyzing the function.
            vis->analyze();

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
            dbgs() << "CTX: ";
            InstructionUtils::printCallingCtx(dbgs(),this->currFuncCallSites,true);
        }
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
            this->processCalledFunction(I, currFunc);
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
                hasTargets = InstructionUtils::getPossibleFunctionTargets(I, targetFunctions);
#ifdef DEBUG_CALL_INSTR
                dbgs() << "Function Pointer targets:" << targetFunctions.size() << "\n";
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
            // get potential target function from a given pointer.
            if(hasTargets) {
                assert(targetFunctions.size() > 0);
#ifdef DEBUG_CALL_INSTR
                dbgs() << "There are: " << targetFunctions.size() << " Target Functions.\n";
#endif
                for(Function *currFunction : targetFunctions) {
                    this->processCalledFunction(I, currFunction);
                }

            } else {

#ifdef DEBUG_CALL_INSTR
                dbgs() << "Function pointer does not point to any functions:";
                calledValue->print(dbgs());
                dbgs() << ", So Ignoring\n";
#endif
            }
        }
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
            _super->visit(inst);
        }
#else
        _super->visit(BB->begin(), BB->end());
#endif
    }

    void GlobalVisitor::analyze() {
        // the traversal order should not be null
        assert(this->traversalOrder != nullptr);
        for(unsigned int i = 0; i < this->traversalOrder->size(); i++){
            // current strongly connected component.
            std::vector<BasicBlock *> *currSCC = (*(this->traversalOrder))[i];
            if(currSCC->size() == 1) {
                this->inside_loop = false;
                for(VisitorCallback *currCallback:allCallbacks) {
                    currCallback->setLoopIndicator(false);
                }
                //Analyzing single basic block.
                for(unsigned int j=0; j < currSCC->size(); j++) {
                    BasicBlock* currBB = (*currSCC)[j];
                    this->visit(currBB);
                }

            } else {
                unsigned long opt_num_to_analyze = BBTraversalHelper::getNumTimesToAnalyze(currSCC);
#ifdef HARD_LOOP_LIMIT
                if (MAX_LOOP_CNT < opt_num_to_analyze) {
                    opt_num_to_analyze = MAX_LOOP_CNT;
                }
#endif
#ifdef DEBUG_GLOBAL_ANALYSIS
                dbgs() << "Analyzing Loop BBS for:" << opt_num_to_analyze <<" number of times\n";
#endif
                this->inside_loop = true;

                for(VisitorCallback *currCallback:allCallbacks) {
                    currCallback->setLoopIndicator(true);
                }

                for(unsigned int l=0; l < opt_num_to_analyze; l++) {
                    // ensure that loop has been analyzed minimum number of times.
                    if(l >= (opt_num_to_analyze-1)) {
                        this->inside_loop = false;
                        for(VisitorCallback *currCallback:allCallbacks) {
                            currCallback->setLoopIndicator(false);
                        }
                    }
                    for (unsigned int j = 0; j < currSCC->size(); j++) {
                        BasicBlock *currBB = (*currSCC)[j];
                        this->visit(currBB);
                    }
                }
#ifdef DEBUG_GLOBAL_ANALYSIS
                dbgs() << "Analyzing Loop BBS END\n";
#endif
                //Analyzing loop.
            }
        }
    }
}

