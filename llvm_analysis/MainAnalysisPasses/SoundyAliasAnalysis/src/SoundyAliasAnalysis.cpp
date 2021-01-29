//
// Created by machiry on 10/24/16.
//
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/ValueSymbolTable.h"
#include "ModuleState.h"
#include <AliasObject.h>
#include <iostream>
#include <fstream>
#include <llvm/Analysis/CallGraph.h>
#include <FunctionChecker.h>
#include <CFGUtils.h>
#include <AliasFuncHandlerCallback.h>
#include <llvm/Analysis/LoopInfo.h>
#include <TaintUtils.h>
#include "AliasAnalysisVisitor.h"
#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/Module.h"
#include "KernelFunctionChecker.h"
#include "TaintAnalysisVisitor.h"
#include "GlobalVisitor.h"
#include "RangeAnalysis.h"
#include "llvm/Support/CommandLine.h"
#include "bug_detectors/BugDetectorDriver.h"
#include "PointsToUtils.h"
#include <chrono>
#include <ctime>
#include "ModAnalysisVisitor.h"
#include "SwitchAnalysisVisitor.h"
#include "PathAnalysisVisitor.h"
#include "llvm/IR/InstIterator.h"
#include "InstHandler.h"


using namespace llvm;
using namespace llvm::sys;

namespace DRCHECKER {

//#define DEBUG_SCC_GRAPH
//#define DEBUG_TRAVERSAL_ORDER
//#define DEBUG_GLOBAL_VARIABLES
//#define DEBUG_GLOBAL_TAINT

#define NETDEV_IOCTL "NETDEV_IOCTL"
#define READ_HDR "READ_HDR"
#define WRITE_HDR "WRITE_HDR"
#define IOCTL_HDR "IOCTL_HDR"
#define DEVATTR_SHOW "DEVSHOW"
#define DEVATTR_STORE "DEVSTORE"
#define V4L2_IOCTL_FUNC "V4IOCTL"
#define NULL_ARG "NULL_ARG"
#define MY_IOCTL "MY_IOCTL"

    std::map<Value *, std::set<PointerPointsTo*>*> GlobalState::globalVariables;
    std::map<Function *, std::set<BasicBlock*>*> GlobalState::loopExitBlocks;

    FunctionHandlerCallback* AliasAnalysisVisitor::callback = new AliasFuncHandlerCallback();
    FunctionHandler* AliasAnalysisVisitor::functionHandler = new FunctionHandler(new KernelFunctionChecker());
    FunctionChecker* TaintAnalysisVisitor::functionChecker = nullptr;

    static cl::opt<std::string> checkFunctionName("toCheckFunction",
                                              cl::desc("Function which is to be considered as entry point "
                                                               "into the driver"),
                                              cl::value_desc("full name of the function"), cl::init(""));

    static cl::opt<std::string> functionType("functionType",
                                              cl::desc("Function Type. \n Linux kernel has different "
                                                               "types of entry points from user space.\n"
                                                               "Specify the type of entry function."),
                                              cl::value_desc("Function Type"), cl::init(""));

    static cl::opt<unsigned> skipInit("skipInit", cl::desc("Skip analyzing init functions."),
                                       cl::value_desc("long, non-zero value indicates, skip initialization function"),
                                       cl::init(1));

    static cl::opt<std::string> outputFile("outputFile",
                                            cl::desc("Path to the output file, where all the warnings should be stored."),
                                            cl::value_desc("Path of the output file."), cl::init(""));

    static cl::opt<std::string> instrWarnings("instrWarnings",
                                              cl::desc("Path to the output file, where all the warnings w.r.t instructions should be stored."),
                                              cl::value_desc("Path of the output file."), cl::init(""));

    static cl::opt<std::string> entryConfig("entryConfig",
                                              cl::desc("Config file that specifies all entry functions to be analyzed and the related information like type and user arg"),
                                              cl::value_desc("The path of the config file"), cl::init(""));
    static cl::opt<string> printPathDir ("PrintPathDir", cl::desc("Print paths to a directory"), cl::init(""));

    

    

    typedef struct FuncInf {
        std::string name;
        Function *func;
        std::string ty;
        std::vector<int> user_args;
    } FuncInf;


    static std::vector<FuncInf*> targetFuncs;

    struct SAAPass: public ModulePass {
    public:
        static char ID;
        //GlobalState moduleState;
        llvm::DataLayout *dl;

        CallGraph *callgraph;
        FunctionChecker *currFuncChecker;

        SAAPass() : ModulePass(ID) {
            currFuncChecker = new KernelFunctionChecker();
        }

        ~SAAPass() {
            delete(currFuncChecker);
        }

		//Copied from online source...
        std::vector<std::string> split(const std::string& str, const std::string& delim) {
    		std::vector<std::string> tokens;
    		size_t prev = 0, pos = 0;
    		do{
        		pos = str.find(delim, prev);
        		if (pos == std::string::npos) pos = str.length();
        		std::string token = str.substr(prev, pos-prev);
        		if (!token.empty()) tokens.push_back(token);
        		prev = pos + delim.length();
    		}while (pos < str.length() && prev < str.length());
    		return tokens;
		}

        Function *getFuncByName(Module &m, std::string &name) {
            for (Function &f : m) {
                if (f.hasName() && f.getName().str() == name) {
                    return &f;
                }
            }
            return nullptr;
        }

        void getTargetFunctions(Module &m) {
            if (checkFunctionName.size() > 0) {
                //Method 0: specify a single entry function.
                FuncInf *fi = new FuncInf();
                fi->name = checkFunctionName;
                fi->func = getFuncByName(m,checkFunctionName);
                //The user arg number might be encoded in the type string if it's MY_IOCTL.
                if (functionType.find(MY_IOCTL) == 0) {
                    fi->ty = MY_IOCTL; 
                    //Get the encoded user arg information.
                    std::vector<std::string> tks = split(functionType,"_");
                    if (tks.size() > 2) {
                        for (int i = 2; i < tks.size(); ++i) {
                            //NOTE: Exceptions may occur if the invalid arg is passed-in.
                            int idx = std::stoi(tks[i]);
                            fi->user_args.push_back(idx);
                        }
                    }
                }else {
                    fi->ty = functionType;
                }
                targetFuncs.push_back(fi);
            }else if (entryConfig.size() > 0) {
                //Method 1: specify one or multiple functions in a config file, together w/ related information like type.
                //Line format:
                //<func_name> <type> <user_arg_no e.g. 1_3_6>
                std::ifstream ifile;
                ifile.open(entryConfig);
                std::string l;
                while (std::getline(ifile, l)) {
                    //Skip the comment line
                    if (l.find("#") == 0) {
                        continue;
                    }
                    std::vector<std::string> tks = split(l," ");
                    if (tks.size() < 2) {
                        dbgs() << "Invalid line in the entry config file: " << l << "\n";
                        continue;
                    }
                    FuncInf *fi = new FuncInf();
                    fi->name = tks[0];
                    fi->func = getFuncByName(m,tks[0]);
                    fi->ty = tks[1];
                    if (tks.size() > 2) {
                        //Get the user arg indices.
                        std::vector<std::string> utks = split(tks[2],"_");
                        for (std::string &s : utks) {
                            int idx = std::stoi(s);
                            fi->user_args.push_back(idx);
                        }
                    }
                    targetFuncs.push_back(fi);
                }
                ifile.close();
            }else {
                //No entry functions specified.
                dbgs() << "getTargetFunctions(): No entry functions specified!\n";
                return;
            }
            //debug output
            dbgs() << "getTargetFunctions: Functions to analyze:\n";
            for (FuncInf *fi : targetFuncs) {
                dbgs() << "FUNC: " << fi->name << " PTR: " << (const void*)fi->func << " TYPE: " << fi->ty << " USER_ARGS:";
                for (int i : fi->user_args) {
                    dbgs() << " " << i;
                }
                dbgs() << "\n";
            }
            return;
        }

        //For any global variable that is used by our specified function(s), find all ".init" functions that also use the same GV.
        //************HZ***********
        //TODO: consider to encode our domain knowledge about the driver interface here, e.g. if the target function is an .ioctl,
        //we can try to identify its related .open and driver .probe in this function, as these functions will possibly do some
        //initializations for some internal shared states like file->private.
        //************HZ***********
        void getAllInterestingInitFunctions(Module &m, std::string currFuncName,
                                            std::set<Function*> &interestingInitFuncs) {
            /***
             * Get all init functions that should be analyzed to analyze provided init function.
             */
            Module::GlobalListType &currGlobalList = m.getGlobalList();
            std::set<llvm::GlobalVariable*> currFuncGlobals;
            bool is_used_in_main;
            std::set<Function*> currFuncs;
            for(Module::global_iterator gstart = currGlobalList.begin(), gend = currGlobalList.end();
                    gstart != gend; gstart++) {
                llvm::GlobalVariable *currGlob = &*gstart;
                currFuncs.clear();
                is_used_in_main = false;
                for(auto cu:currGlob->users()) {
                    Instruction *currInst = dyn_cast<Instruction>(cu);
                    if(currInst != nullptr && currInst->getParent() && currInst->getParent()->getParent()) {
                        Function *currFunc = currInst->getParent()->getParent();
                        if(currFunc->hasName()) {
                            if(currFunc->getName() == currFuncName) {
                                is_used_in_main = true;
#ifdef DEBUG_GLOBAL_VARIABLES
                                dbgs() << "Global variable:" << *gstart << " used in function:" << currFuncName << "\n";
#endif
                            } else {
                                if(currFuncChecker->is_init_function(currFunc)) {
                                    currFuncs.insert(currFunc);
                                }
                            }
                        }
                    }
                }
                //"currFuncs" contains all _init_ functions that have used current gv, 
                //"is_used_in_main" indicates whether current gv is used in the target function to analyze.
                //The assumption here is that we will never use an _init_ function as the target function.
                if(is_used_in_main && currFuncs.size()) {
                    for(auto cg:currFuncs) {
                        if(interestingInitFuncs.find(cg) != interestingInitFuncs.end()) {
                            interestingInitFuncs.insert(cg);
                        }
                    }
                }

            }

        }

        bool runOnModule(Module &m) override {

            struct Input *input = getInput(m);

            if (input == NULL) {
                errs() << "Can not locate the vulnerable site\n";
                return true;
            }

            //The first is head, let skip it.
            input = input->next;

            for(auto i = input; i != NULL; i = i->next){
                   errs() << "basepointer is: " << *(i->basePointer);
                   errs() << "size of obj:" << getSizeOfObj(i->basePointer) << "\n";
                }

            for(auto tmpsite : calltrace){
                    if(tmpsite->F == nullptr){
                        
                        errs() << tmpsite->funcName << "\n";
                    }
                }

            FunctionChecker* targetChecker = new KernelFunctionChecker();
            // create data layout for the current module
            DataLayout *currDataLayout = new DataLayout(&m);

            // for(auto callsite : calltrace){
            //     errs() << callsite->funcName << "\t" << callsite->filePath <<"\n";
            // }
            setupGlobals(m);
            dbgs() << "Setup global variables done" << "\n";
            this->printCurTime();

            int filecount = 0;
            int depth = 0;
            std::set<Instruction *> visitedusesites;
            for(auto callsite : calltrace){
                if(foundTerminatingFunc){
                    break;
                }
                /*if(depth >= 5 || depth++ >= calltrace.size()){
                    break;
                }*/

                if(!callsite->F){
                    findNextFuncInModule();
                    //continue;
                }
                GlobalState currState(currDataLayout);
                // set the read and write flag in global state, to be used by differect detectors.
                //TODO: this should be moved to the bug detect phase for every entry function.
                //currState.is_read_write_function = functionType == READ_HDR || functionType == WRITE_HDR;
                // set pointer to global state
                AliasAnalysisVisitor::callback->setPrivateData(&currState);
                // setting function checker(s).
                TaintAnalysisVisitor::functionChecker = targetChecker;
                AliasAnalysisVisitor::callback->targetChecker = targetChecker;
                for(auto visitedusesite : visitedusesites){
                    currState.visitedsites.insert(visitedusesite);
                }

                currState.entryfunc = callsite->F;
                currState.filecounter = filecount;
                currState.printPathDir = printPathDir;

                int CallTracePointer = 0;

                

                for(auto tmpsite : calltrace){
                    auto sitefunc = tmpsite->F;
                    auto csi = new callsiteinfo();
                    csi->funcname = tmpsite->funcName;
                    csi->func = sitefunc;
                    csi->filename = tmpsite->filePath;
                    csi->linenum = tmpsite->line;
                    currState.callsiteinfos.push_back(csi);
                    if(tmpsite->funcName == callsite->funcName){
                        currState.calltracepointer = CallTracePointer;
                        currState.calltracebasepointer = CallTracePointer;
                        break;
                    }
                    CallTracePointer++;
                }
                // currState.interestinginst = input->inst;
                // dbgs() << input->func->getName().str() << "\n";

                for(auto i = input; i != NULL; i = i->next){
                    currState.baseptrmap[i->inst].insert(i->basePointer);
                    if(currState.offset4baseptrs.find(i->basePointer) != currState.offset4baseptrs.end()){
                        if(i->offset < currState.offset4baseptrs[i->basePointer]){
                            currState.offset4baseptrs[i->basePointer] = i->offset;
                        }
                    }else{
                        currState.offset4baseptrs[i->basePointer] = i->offset;
                    }
                    errs() << "vulsite: ";
                    i->inst->print(errs());
                    errs() << "\n";
                    if(i->topCallsite){
                        currState.topcallsites.insert(i->topCallsite);
                    }
                }



                //Get the target functions to be analyzed.
                //getTargetFunctions(m);

                auto t_start = std::chrono::system_clock::now();
                dbgs() << "[TIMING] Analysis starts at: ";
                this->printCurTime();
                // Call init functions.
                //hz: this is a lightweight (i.e. only includes alias analysis) analysis for the init functions (e.g. .open and .probe), 
                //the goal is to set up some preliminary point-to records used in the real target functions.
                dbgs() << "=========================Preliminary Analysis Phase=========================\n";
                currState.analysis_phase = 1;

                auto t_prev = std::chrono::system_clock::now();
                auto t_next = t_prev;
                dbgs() << "=========================Main Analysis Phase=========================\n";
                currState.analysis_phase = 2;
                if (!currState.entryfunc)
                    return false;
                Function &currFunction = *currState.entryfunc;

                std::vector<std::vector<BasicBlock *> *> *traversalOrder = BBTraversalHelper::getSCCTraversalOrder(currFunction);
    #ifdef DEBUG_TRAVERSAL_ORDER
                std::cout << "Got Traversal order For: " << currFunction.getName().str() << "\n";
                BBTraversalHelper::printSCCTraversalOrder(traversalOrder,&dbgs());
    #endif
    #ifdef DEBUG_SCC_GRAPH
                InstructionUtils::dumpFuncGraph(&currFunction);
    #endif
                // first instruction of the entry function, used in the initial calling context.
                std::vector<Instruction*> *pcallSites = new std::vector<Instruction*>();
                errs() << "currFunction: " << currFunction.getName().str() << "\n";
                pcallSites->push_back(currFunction.getEntryBlock().getFirstNonPHIOrDbg());
                

                std::vector<VisitorCallback *> allCallBacks;
                // add pre analysis bug detectors/
                // these are the detectors, that need to be run before all the analysis passes.
                //BugDetectorDriver::addPreAnalysisBugDetectors(currState, &currFunction, pcallSites,
                //                                              &allCallBacks, targetChecker);

                // first add all analysis visitors.
                addAllVisitorAnalysis(currState, &currFunction, pcallSites, &allCallBacks);

                // next, add all bug detector analysis visitors, which need to be run post analysis passed.
                //BugDetectorDriver::addPostAnalysisBugDetectors(currState, &currFunction, pcallSites,
                //                                               &allCallBacks, targetChecker);

                // create global visitor and run it.
                GlobalVisitor *vis = new GlobalVisitor(currState, &currFunction, pcallSites, traversalOrder, allCallBacks);

                //SAAVisitor *vis = new SAAVisitor(currState, &currFunction, pcallSites, traversalOrder);
                //dbgs() << "CTX: " << fi->name << " ->\n";
    #ifdef TIMING
                dbgs() << "[TIMING] Start func(1) " << currState.entryfunc->getName().str() << ": ";
                auto t0 = InstructionUtils::getCurTime(&dbgs());
    #endif
                DRCHECKER::currEntryFunc = &currFunction;

                vis->analyze();

                filecount = currState.filecounter;

                for(auto usesite : currState.visitedsites){
                    visitedusesites.insert(usesite);
                }

    #ifdef TIMING
                dbgs() << "[TIMING] End func(1) " << currState.entryfunc->getName().str() << " in: ";
                InstructionUtils::getTimeDuration(t0,&dbgs());
    #endif
                //Record the timestamp.
                t_next = std::chrono::system_clock::now();
                std::chrono::duration<double> elapsed_seconds = t_next - t_prev;
                dbgs() << "[TIMING] Anlysis of " << currState.entryfunc->getName().str() << " done in : " << elapsed_seconds.count() << "s\n";
                t_prev = t_next;

                //clean up
                dbgs() << "[TIMING] Clean up GlobalVisitor at: ";
                this->printCurTime();
                delete(vis);

                auto t_now = std::chrono::system_clock::now();
                elapsed_seconds = t_now - t_start;
                dbgs() << "[TIMING] All main anlysis done in : " << elapsed_seconds.count() << "s\n";

            }

            if (!foundTerminatingFunc) {
                dbgs() << "No terminating func found untill end\n";
            }

            dbgs() << "Clean up global state at: ";
            this->printCurTime();
            //currState.cleanup();
            dbgs() << "Clean up DataLayout at: ";
            this->printCurTime();
            //delete(currDataLayout);
            dbgs() << "All done: ";
            this->printCurTime();

            exit(0);
            return true;
        }

        void printCurTime() {
            auto t_now = std::chrono::system_clock::now();
            std::time_t now_time = std::chrono::system_clock::to_time_t(t_now);
            dbgs() << std::ctime(&now_time) << "\n";
        }

        void addAllVisitorAnalysis(GlobalState &targetState,
                                   Function *toAnalyze,
                                   std::vector<Instruction*> *srcCallSites,
                                   std::vector<VisitorCallback*> *allCallbacks) {

            // This function adds all analysis that need to be run by the global visitor.
            // it adds analysis in the correct order, i.e the order in which they need to be
            // run.

            VisitorCallback *currVisCallback = new AliasAnalysisVisitor(targetState, toAnalyze, srcCallSites);

            // first add AliasAnalysis, this is the main analysis needed by everyone.
            allCallbacks->push_back(currVisCallback);

            currVisCallback = new TaintAnalysisVisitor(targetState, toAnalyze, srcCallSites);

            // next add taint analysis.
            allCallbacks->push_back(currVisCallback);

            // then the path analysis, which may need the info provided by the previous two analyses.
            // currVisCallback = new PathAnalysisVisitor(targetState, toAnalyze, srcCallSites);

            // allCallbacks->push_back(currVisCallback);
            /*
            //hz: add the 3rd basic analysis: mod analysis to figure out which instructions can modify the global states.
            currVisCallback = new ModAnalysisVisitor(targetState, toAnalyze, srcCallSites);

            // next add mod analysis.
            allCallbacks->insert(allCallbacks->end(), currVisCallback);

            //hz: add the 4th basic analysis: switch analysis to figure out the mapping between "cmd" value and BBs in the ioctl().
            currVisCallback = new SwitchAnalysisVisitor(targetState, toAnalyze, srcCallSites);

            // next add mod analysis.
            allCallbacks->insert(allCallbacks->end(), currVisCallback);
            */
        }

        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.setPreservesAll();
            //AU.addRequired<RangeAnalysis::InterProceduralRA<RangeAnalysis::CropDFS>>();
            AU.addRequired<CallGraphWrapperPass>();
            AU.addRequired<LoopInfoWrapperPass>();
        }

    private:

        void printGVInfo(GlobalVariable &gv) {
            gv.print(dbgs());
            dbgs() << " NUM USES:" << gv.getNumUses() << ", TYPE:";
            gv.getType()->print(dbgs());
            //op1->print(dbgs());
            dbgs() << "\n";

            dbgs() << "For:";
            dbgs() << gv.getName() << ":";
            dbgs() << " of type (" << gv.getType()->getContainedType(0)->isStructTy() << ","
                   << gv.getType()->isPointerTy() << "," << gv.getType()->isArrayTy() << "):";
            gv.getType()->print(dbgs());
            dbgs() << ":";
            if(gv.hasInitializer()) {
                Constant *initializationConst = gv.getInitializer();
                initializationConst->getType()->print(dbgs());
                dbgs() << ", Struct Type:" << initializationConst->getType()->isStructTy();
                if(initializationConst->getType()->isStructTy() &&
                        !initializationConst->isZeroValue()) {
                    ConstantStruct *constantSt = dyn_cast<ConstantStruct>(initializationConst);
                    dbgs() << " Num fields:" << constantSt->getNumOperands() << "\n";
                    for (int i = 0; i < constantSt->getNumOperands(); i++) {
                        dbgs() << "Operand (" << i + 1 << ") :";
                        Function *couldBeFunc = dyn_cast<Function>(constantSt->getOperand(i));
                        dbgs() << "Is Function:" << (couldBeFunc != nullptr) << "\n";
                        if(!couldBeFunc)
                            constantSt->getOperand(i)->print(dbgs());
                        dbgs() << "\n";
                    }
                }
                dbgs() << "\n";
            } else {
                dbgs() << "No initializer\n";
            }
        }

        void setupGlobals(Module &m) {
            /***
             * Set up global variables.
             */
            // map that contains global variables to AliasObjects.
            std::map<Value*, AliasObject*> globalObjectCache;
            std::vector<llvm::GlobalVariable*> visitorCache;
            visitorCache.clear();
            // first add global functions.
            for(Module::iterator mi = m.begin(), ei = m.end(); mi != ei; mi++) {
                GlobalState::addGlobalFunction(&(*mi), globalObjectCache);
            }
            Module::GlobalListType &currGlobalList = m.getGlobalList();
            for (Module::global_iterator gstart = currGlobalList.begin(), gend = currGlobalList.end(); gstart != gend; gstart++) {
                //We cannot simply ignore the constant global structs (e.g. some "ops" structs are constant, but we still need
                //to know their field function pointers to resolve the indirect call sites involving them).
                /*
                // ignore constant immutable global pointers
                if((*gstart).isConstant()) {
                    continue;
                }
                */
                if (!GlobalState::toCreateObjForGV(&(*gstart))) {
                    continue;
                }
                GlobalState::addGlobalVariable(visitorCache, &(*gstart), globalObjectCache);
#ifdef DEBUG_GLOBAL_VARIABLES
                printGVInfo(*gstart);
#endif
                // sanity
                assert(visitorCache.empty());
            }
            globalObjectCache.clear();
            // OK get loop info of all the functions and store them for future use.
            // get all loop exit basic blocks.
            for(Module::iterator mi = m.begin(), ei = m.end(); mi != ei; mi++) {
                Function &currFunction = *mi;
                if(!currFunction.isDeclaration()) {
                    LoopInfoWrapperPass &p = getAnalysis<LoopInfoWrapperPass>(currFunction);
                    LoopInfo &funcLoopInfo = p.getLoopInfo();
                    SmallVector<BasicBlock *, 1000> allExitBBs;
                    allExitBBs.clear();
                    for (auto a:funcLoopInfo) {
                        a->getExitingBlocks(allExitBBs);
                        GlobalState::addLoopExitBlocks(&currFunction, allExitBBs);
                        allExitBBs.clear();
                    }
                }
            }
        }

        void setupFunctionArgs(FuncInf *fi, GlobalState &targetState, std::vector<Instruction*> *callSites) {
            if (!fi || !fi->func) {
                dbgs() << "!!! setupFunctionArgs(): (!fi || !fi->func)\n";
                return;
            }
            /***
             * Set up the function args for the main entry function(s).
             */
            targetState.getOrCreateContext(callSites);

            // arguments which are tainted and passed by user
            std::set<unsigned long> taintedArgs;
            // arguments which contain tainted data
            std::set<unsigned long> taintedArgData;
            // arguments which are pointer args
            std::set<unsigned long> pointerArgs;
            bool is_handled = false;
            if(fi->ty == IOCTL_HDR) {
                // last argument is the user pointer.
                taintedArgs.insert(fi->func->arg_size() - 1);
                // first argument is the file pointer
                pointerArgs.insert(0);
                is_handled = true;
            }
            //hz: We want to set all global variables as taint source,
            //for ioctl() in driver code, the FILE pointer should also
            //be regarded as a global variable.
            if(fi->ty == MY_IOCTL) {
                //Any user arg indices?
                if (fi->user_args.size() > 0) {
                    for (int i : fi->user_args) {
                        taintedArgs.insert(i);
                    }
                }else {
                    //by default the last argument is the user pointer.
                    taintedArgs.insert(fi->func->arg_size() - 1);
                }
                is_handled = true;
            }
            if(fi->ty == READ_HDR || fi->ty == WRITE_HDR) {
                taintedArgs.insert(1);
                taintedArgs.insert(2);
                //hz: for now we don't add the args to the "pointerArgs" and create the Arg objects for them, because later in the analysis
                //we will create the objs on demand.
                //pointerArgs.insert(0);
                //pointerArgs.insert(3);
                is_handled = true;
            }
            if(fi->ty == V4L2_IOCTL_FUNC) {
                taintedArgData.insert(fi->func->arg_size() - 1);
                for(unsigned long i=0;i<fi->func->arg_size(); i++) {
                    pointerArgs.insert(i);
                }
                is_handled = true;
            }
            if(fi->ty == DEVATTR_SHOW) {
                for(unsigned long i=0;i<fi->func->arg_size(); i++) {
                    pointerArgs.insert(i);
                }
                is_handled = true;
            }
            if(fi->ty == DEVATTR_STORE) {
                if(fi->func->arg_size() == 3) {
                    // this is driver attribute
                    taintedArgData.insert(1);
                } else {
                    // this is device attribute
                    taintedArgData.insert(2);
                }
                for (unsigned long i = 0; i < fi->func->arg_size() - 1; i++) {
                    pointerArgs.insert(i);
                }
                is_handled = true;
            }
            if(fi->ty == NETDEV_IOCTL) {
                taintedArgData.insert(1);
                for(unsigned long i=0;i<fi->func->arg_size()-1; i++) {
                    pointerArgs.insert(i);
                }
                is_handled = true;
            }
            //hz: the function doesn't have arguments. This is created for test purposes.
            if(fi->ty == NULL_ARG) {
                is_handled = true;
            }
            if(!is_handled) {
                dbgs() << "Invalid Function Type:" << fi->ty << "\n";
                dbgs() << "Errorring out\n";
            }
            assert(is_handled);


            std::map<Value*, std::set<PointerPointsTo*>*> *currPointsTo = targetState.getPointsToInfo(callSites);
            //Create the InstLoc for the function entry.
            Instruction *ei = fi->func->getEntryBlock().getFirstNonPHIOrDbg();
            std::vector<Instruction*> *ctx = new std::vector<Instruction*>();
            ctx->push_back(ei);
            InstLoc *loc = new InstLoc(ei,ctx);
            unsigned long arg_no=0;
            for(Function::arg_iterator arg_begin = fi->func->arg_begin(), arg_end = fi->func->arg_end(); arg_begin != arg_end; arg_begin++) {
                Value *currArgVal = &(*arg_begin);
                if (taintedArgs.find(arg_no) != taintedArgs.end()) {
                    //hz: Add a taint tag indicating that the taint is from user-provided arg, instead of global states.
                    //This tag represents the "arg", at the function entry its point-to object hasn't been created yet, so no "pobjs" for the tag.
                    TaintTag *currTag = new TaintTag(0,currArgVal,false);
                    TaintFlag *currFlag = new TaintFlag(loc, true, currTag);
                    std::set<TaintFlag*> *currTaintInfo = new std::set<TaintFlag*>();
                    currTaintInfo->insert(currFlag);
                    TaintUtils::updateTaintInfo(targetState, callSites, currArgVal, currTaintInfo);
                }
                if (pointerArgs.find(arg_no) != pointerArgs.end()) {
                    AliasObject *obj = new FunctionArgument(currArgVal, currArgVal->getType(), fi->func, callSites);
                    obj->addPointerPointsTo(currArgVal,loc);
                    //Record the pto in the global state.
                    if (currPointsTo) {
                        PointerPointsTo *pto = new PointerPointsTo(currArgVal,obj,0,loc,false);
                        if (currPointsTo->find(currArgVal) == currPointsTo->end()) {
                            (*currPointsTo)[currArgVal] = new std::set<PointerPointsTo*>();
                        }
                        (*currPointsTo)[currArgVal]->insert(pto);
                    }
                    if(taintedArgData.find(arg_no) != taintedArgData.end()) {
                        //In this case the arg obj should be treated as a user-initiated taint source.
                        obj->setAsTaintSrc(loc,false);
                    }
                } else {
                    assert(taintedArgData.find(arg_no) == taintedArgData.end());
                }
                arg_no++;
            }
        }

        //hz: try to set all global variables as taint source.
        void addGlobalTaintSource(GlobalState &targetState) {
            //Type of globalVariables: std::map<Value *, std::set<PointerPointsTo*>*>
            for (auto const &it : GlobalState::globalVariables) {
                Value *v = it.first;
                std::set<PointerPointsTo*> *ps = it.second;
                if (!v || !ps || ps->empty()) {
                    continue;
                }
                GlobalVariable *gv = dyn_cast<GlobalVariable>(v);
                //Exclude the constants which cannot be modified.
                if (gv && gv->isConstant()) {
                    continue;
                }
                //Don't set as taint source for several object types, e.g. function.
                if (v->getType() && v->getType()->isPointerTy()) {
                    Type *ty = v->getType()->getPointerElementType();
                    //Exclude certain types, e.g. function.
                    if (ty->isFunctionTy() || ty->isLabelTy() || ty->isMetadataTy()) {
                        continue;
                    }
                }
#ifdef DEBUG_GLOBAL_TAINT
                dbgs() << "addGlobalTaintSource(): Set the glob var as taint source: " << InstructionUtils::getValueStr(v) << "\n";
#endif
                InstLoc *loc = new InstLoc(v,nullptr);
                for(auto const &p : *ps){
                    if (!p->targetObject) {
                        continue;
                    }
                    //Exclude the const object.
                    if (p->targetObject->is_const) {
                        continue;
                    }
                    p->targetObject->setAsTaintSrc(loc,true);
#ifdef DEBUG_GLOBAL_TAINT
                    dbgs() << "addGlobalTaintSource(): Set the alias obj as taint source:\n";
                    dbgs() << "Object Type: " << InstructionUtils::getTypeStr(p->targetObject->targetType) << "\n";
                    dbgs() << " Object Ptr: " << InstructionUtils::getValueStr(p->targetObject->getObjectPtr()) << "\n";
#endif
                }
            }
        }
        struct Input *getInput(Module &M) {
            locatePointerAndOffset(M);
            if (!head)
                return head;
            for (struct Input *i = head->next; i != NULL; i=i->next) {
                uint64_t size = getSizeOfObj(i->basePointer);
                if (i->distance > minDistance || size > i->size) {
                    errs() << "unlink " << i << "\n";
                    struct Input *next = i->next;
                    struct Input *prev = i->prev;
                    if (next != NULL)
                        next->prev = prev;
                    if (prev != NULL)
                        prev->next = next;
                    free(i);
                }
            }
            return head;
        }

        void locatePointerAndOffset(Module &M) {
            uint64_t size = BUG_Size;
            dlForInput = new llvm::DataLayout(&M);
            bool BUG_in_header = false;
            parseCalltrace(&M);
            minDistance = MAX_DISTANCE * calltrace.size();
            tmpDistance = MAX_DISTANCE * calltrace.size();
            unsigned long *ret = getFirstValidItemInCalltrace();
            if (ret == NULL)
                return;
            CalltraceItem *item = (CalltraceItem *)ret[0];
            int index = ret[1];
            if (item == NULL) {
                errs() << "calltrace is empty\n";
                return;
            }
            if (item->F == NULL) {
                errs() << "Can not find function " << item->funcName << " in one.bc\n";
                return;
            }
            auto F = item->F;
            errs() << "item->funcName: " << item->funcName << "\n";
            if (item->funcBound[0] > BUG_Func_Line)
                BUG_in_header = true;
            inst_iterator I = inst_begin(*F), E = inst_end(*F);
            for (; I != E; ++I) {
                llvm::DebugLoc dbgloc = (*I).getDebugLoc();
                if (!BUG_in_header && !dbgloc) {
                    //errs() << (*I) << "\n";
                    continue;
                }
                int curLine = 0;
                string fileName;
                // dbgloc.get() is used to check the existance of dbg info
                if (!dbgloc.get() || !dbgloc->getLine()) {
                    if (isInst<LoadInst>(&(*I)))
                        inspectInst<LoadInst, Load>(&(*I), dbgloc, NULL, 0, index);
                    continue;
                }
                fileName = dbgloc->getFilename().str();
                curLine = dbgloc->getLine();
                //errs() << fileName << ":" << curLine << "\n";
                //errs() << (*I) << "\n";
                /*if (curLine >= func_bound[0] && curLine <= func_bound[1]) {
                    if (curLine < BUG_Func_Line && basePointer != NULL)
                        break;
                }*/
                if (BUG_in_header) {
                    if (isInst<LoadInst>(&(*I)))
                        inspectInst<LoadInst, Load>(&(*I), dbgloc, NULL, 0, index);
                    continue;
                }
                if (isInCallTrace(fileName, curLine)) {
                    //if ((curLine == BUG_Vul_Line && stripFileName(dbgloc->getFilename().str()) == BUG_Vul_File)) {
                    //   errs() << "target site found: " << (*I) << "\n";
                        //if (isGEPInst(I))
                        //    inspectGEPInst(I);
                        if (isInst<CallInst>(&(*I)))
                            inspectInst<CallInst, Call>(&(*I), dbgloc, NULL, 0, index);
                        if (isInst<LoadInst>(&(*I)))
                            inspectInst<LoadInst, Load>(&(*I), dbgloc, NULL, 0, index);
                    //}
                }
            }
            errs() << "the end\n";
            return;
        }

        unsigned long *getFirstValidItemInCalltrace() {
            unsigned long ret[2];
            int n = 0;
            for (auto it = calltrace.begin(); it != calltrace.end(); it++) {
                if ((*it)->numDuplication == 1) {
                    ret[0] = (unsigned long)*it;
                    ret[1] = n;
                    return ret;
                }
                n++;
            }
            return NULL;
        }

        template <class T>
        bool isInst(Instruction *I) {
            if (T *load = dyn_cast<T>(I))
                return true;
            return false;
        }

        //void inspectCallInst(llvm::Instruction *I, llvm::DebugLoc dbgloc) {
        //    dbglocMatch(dbgloc, )
        //}

        template <class InstType, class T>
        void inspectInst(llvm::Instruction *I, llvm::DebugLoc dbgloc, InstType *realSrc, int deep, int index) {
            bool match = false;
            T::printSloganHeader(I);
            if (dbgloc->getLine() == 0) {
                PHINode *phi = nullptr;
                auto block = (*I).getParent();
                // If load inst doesn't have a valid dbg info, 
                // it means this load inst may belongs to a phi inst
                // we check out phi inst before load inst to eliminate 
                // the incorrectness of dbg info
                for (Instruction &I1 : *block) {
                    if (isa<PHINode>(I1)) {
                        phi = dyn_cast<PHINode>(&(I1));
                        break;
                    }
                    if (&I1 == &(*I))
                        break;
                }
                if (phi != nullptr and deep < 3) {
                    int n = phi->getNumIncomingValues();
                    for (int i=0; i<n; i++) {
                        auto v = phi->getIncomingValue(i);
                        llvm::Instruction *incomingI = dyn_cast<Instruction>(v);
                        if (incomingI == nullptr)
                            continue;
                        // No Matryoshka doll
                        if (incomingI == I)
                            continue;
                        if (isa<Instruction>(incomingI)) {
                            auto icomDbgloc = incomingI->getDebugLoc();
                            if (!icomDbgloc)
                                continue;
                            errs() << "one of the phi incoming\n";
                            if (realSrc == NULL) {
                                realSrc = T::convertType(I);                          
                            }
                            inspectInst<InstType, T>(incomingI, icomDbgloc, realSrc, deep+1, index);
                            //errs() << dbgloc->getFilename().str() << ":" << dbgloc->getLine() << "\n";
                            //match = matchCalltrace(dbgloc, &index);
                            //if (index >= 0 && match)
                                //match = matchLastCaller(index, dbgloc);
                        }
                    }
                }
            }
            match = matchCalltrace(dbgloc, &index);
            if (index >= 0 && match)
                match = matchLastCaller(index, dbgloc);
            if (match) {
                if (realSrc) {
                    if (T::isInst(realSrc))
                        T::handleInst(realSrc);
                } else {
                    if (T::isInst(I)) {
                        InstType *inst = T::convertType(I);
                        T::handleInst(inst);
                    }
                }
            }
            //printDistance();
            T::printSloganTail();
        }

        void inspectGEPInst(inst_iterator I) {
            if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(&(*I))) {
                errs() << (*I) << "\n";
                errs() << "Found a GEP instruction" << gep << "\n";
            }
        }

        int accumulateDistance() {
            int ret = 0;
            for (vector<CalltraceItem*>::iterator it = calltrace.begin(); it != calltrace.end(); it++) {
                if ((*it)->distance > 0)
                    ret += (*it)->distance;
                else
                    ret -= (*it)->distance;
            }
            return ret;
        }

        bool matchLastCaller(int index, llvm::DebugLoc dbgloc) {
            bool match;
            string fileName = stripFileName(dbgloc->getFilename().str());
            int line = dbgloc->getLine();
            errs() << index;
            match = calltrace[index]->filePath == fileName && \
                        calltrace[index]->line == line;
            if (match) {
                match = true;
                tmpDistance = 0;
                errs() << "--> " << calltrace[index]->filePath << ":" << calltrace[index]->line << " True" << "\n";
            } else {
                int tmp = abs(calltrace[index]->line - line);
                match = false;
                if (tmp <= minDistance) {
                    tmpDistance = tmp;
                    match = true;
                }
                errs() << "--> " << calltrace[index]->filePath << ":" << calltrace[index]->line << " False" << "\n";
            }
            errs() << fileName << ":" << line << " " << calltrace[index]->filePath << ":" << calltrace[index]->line <<"\n";
            return match;
        }

        bool matchCalltrace(llvm::DebugLoc dbgloc, int *index) {
            bool ret = false;
            auto inlineDbg = dbgloc->getInlinedAt();
            if (inlineDbg == NULL) {
                return true;
            }
            (*index)++;
            int curLine = inlineDbg->getLine();
            string fileName = inlineDbg->getFilename().str();
            /*for (vector<CalltraceItem*>::iterator it = calltrace.begin(); it != calltrace.end(); it++) {
                if ((*it)->filePath == stripFileName(fileName) && \
                        curLine >= (*it)->funcBound[0] && curLine <= (*it)->funcBound[1]) {
                    (*it)->distance = (*it)->line - curLine;
                    ret = true;
                }
            }*/
            ret = matchCalltrace(inlineDbg, index);
            if (*index >= 0 && ret) {
                auto item = calltrace[*index];
                errs() << *index;
                ret = item->filePath == stripFileName(fileName) && item->line == curLine;
                if (ret) {
                    errs() << "--> " << fileName << ":" << curLine << " True" << "\n";
                } else {
                    errs() << "--> " << fileName << ":" << curLine << " False" << "\n";
                }
                (*index)--;
                errs() << stripFileName(fileName) << ":" << curLine << " " << item->filePath << ":" << item->line  <<"\n";
            }
            return ret;
        }

        void printDistance() {
            for (vector<CalltraceItem*>::iterator it = calltrace.begin(); it != calltrace.end(); it++) {
                errs() << "filePath:" << (*it)->filePath << " funcName:" << (*it)->funcName << " line:" << (*it)->line << " distance:" << (*it)->distance << " bounds:" << (*it)->funcBound[0] << "-" << (*it)->funcBound[1] << "\n";
            }
        }

        bool isInCallTrace(string fileName, int curLine) {
            bool ret = false;
            string sFileName = stripFileName(fileName);
            for (vector<CalltraceItem*>::iterator it = calltrace.begin(); it != calltrace.end(); it++) {
                //errs() << "filePath: " << (*it)->filePath << " fileName: " << sFileName << "\n";
                if ((*it)->filePath == sFileName) {
                    if (curLine >= (*it)->funcBound[0] && curLine <= (*it)->funcBound[1]) {
                        (*it)->distance = (*it)->line - curLine;
                        ret = true;
                    }
                }
            }
            return ret;
        }

        void parseCalltrace(Module *M) {
            string line;
            vector<string> strlist;
            ifstream fin;
            TheModule = M;
            fin.open(Calltrace_File);
            while (getline(fin, line)) {
                //errs() << line << "\n";
                strlist = splitBy(line, " ");
                if (strlist.size() < 4) {
                    errs() << "size of strlist is less than 4: " << line << "\n";
                    continue;
                }
                CalltraceItem *item = new CalltraceItem;
                item->funcName = strlist[0];
                vector<string> pathlist = splitBy(strlist[1], ":");
                if (pathlist.size() != 2) {
                    errs() << "size of pathlist is not two: " << strlist[1] << "\n";
                    continue;
                }
                item->filePath = pathlist[0];
                item->line = stoi(pathlist[1], nullptr);
                item->isInline = false;
                item->distance = MAX_DISTANCE;
                item->F = NULL;
                item->numDuplication = 0;
                item->funcBound[0] = stoi(strlist[2], nullptr);
                item->funcBound[1] = stoi(strlist[3], nullptr);
                if (strlist.size() == 5)
                    item->isInline = true;
                calltrace.push_back(item);
                //errs() << "funcName:" << item->funcName << " filePath:" << item->filePath << " isInline:" << item->isInline << " line:" << item->line <<"\n";
            }
            findNextFuncInModule();
        }

        void findNextFuncInModule() {
            if (TheModule == NULL) {
                errs() << "Where is the module?\n";
            }
            CalltraceItem *item;
            map<string, llvm::Function*> func_contexts;
            int n=-1;
            for (int i=0; i<calltrace.size(); i++) {
                item = calltrace[i];
                if (item->F != NULL)
                    continue;
                if (n == -1)
                    n = i;
                string func_regx = item->funcName + "(\\.\\d+)?";
                for(auto &F : (*TheModule)){
                    if (F.isIntrinsic())
                        continue;
                    if (regex_match(F.getName().str(), regex(func_regx))) {
                        func_contexts[F.getName().str()] = &F;
                        item->F = &F;
                        item->numDuplication++;
                        //break;
                    }
                }
                
                if (item->numDuplication == 1)
                    break;
            }
            for (int i=n; i < calltrace.size(); i++) {
                errs() << calltrace[i]->funcName << " has " << calltrace[i]->numDuplication <<  " duplications\n";
                if (calltrace[i]->numDuplication == 1) {
                    determineCorrectContext(i, func_contexts);
                    break;
                }
            }
        }

        bool dbglocMatch(llvm::DebugLoc dbgloc, string fileName, int line) {
            string dbgFileName = stripFileName(dbgloc->getFilename().str());
            int dbgLine = dbgloc->getLine();
            return fileName == dbgFileName && line == dbgLine;
        }

        void determineCorrectContext(int n, map<string, llvm::Function*> func_contexts) {
            for (int i=n; i>0; i--) {
                CalltraceItem *nextItem;
                int offset = 1;
                bool flagStop = false;
                do {
                    if (i-offset < 0) {
                        flagStop = true;
                        break;
                    }
                    nextItem = calltrace[i-offset];
                    offset++;
                    if (nextItem->numDuplication > 1)
                        break;
                } while(true);
                if (flagStop)
                    break;
                CalltraceItem *item = calltrace[i];
                auto F = item->F;
                if (item->F == NULL) {
                    errs() << "Can not find " << item->funcName << " in bc\n";
                    return;
                }
                inst_iterator I = inst_begin(*F), E = inst_end(*F);
                errs() << item->filePath << ":" << item->line << "\n";
                for (; I != E; ++I) {
                    llvm::DebugLoc dbgloc = (*I).getDebugLoc();
                    if (!dbgloc)
                        continue;
                    //errs() << (*I) << "\n";
                    //errs() << dbgloc->getFilename().str() << ":" << dbgloc->getLine() << "\n";
                    if (isInst<CallInst>(&(*I)) && dbglocMatch(dbgloc, item->filePath, item->line)) {
                        CallInst *call = dyn_cast<CallInst>(&(*I));
                        llvm::Function *callee = call->getCalledFunction();
                        if (!callee)
                            continue;
                        errs() << "callee " << callee->getName().str() << "\n";
                        string func_regx = nextItem->funcName + "(\\.\\d+)?";
                        if (regex_match(callee->getName().str(), regex(func_regx))) {
                            errs() << nextItem->funcName << "=" << callee->getName().str() << "\n";
                            nextItem->F = func_contexts[callee->getName().str()];
                            nextItem->numDuplication = 1;
                            errs() << nextItem->funcName << "\'s context has been determined\n";
                            break;
                        }
                    }
                }
            }
        }

        vector<string> splitBy(string s, string delimiter) {
            vector<string> ret;
            size_t pos = 0;
            while ((pos = s.find(delimiter)) != std::string::npos) {
                ret.push_back(s.substr(0, pos));
                s.erase(0, pos + delimiter.length());
            }
            ret.push_back(s);
            return ret;
        }

        void typeMatchFunc(Module &M, struct Input *input) {
            llvm::StringRef basePointerStructName;
            input->basePointer->print(errs());
            llvm::Type *type = input->basePointer->getType();
            llvm::Type *pointToType = type->getPointerElementType();
            llvm::Value *op;
            //errs() << "t1 " << type->getTypeID() << " t2 " << type->getPointerElementType()->getTypeID() << "\n";
            if (pointToType->isStructTy()){
                errs() << "\nname: " << pointToType->getStructName() << "\n";
                basePointerStructName = pointToType->getStructName();
            }

            for(auto &F : M){
                for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
                    if(LoadInst *load = dyn_cast<LoadInst>(&(*I))) {
                        op = load->getPointerOperand();
                    } else if(StoreInst *store = dyn_cast<StoreInst>(&(*I))) {
                        op = store->getPointerOperand();
                    } /*else if(CallInst *call = dyn_cast<CallInst>(&(*I))) {
                        if (call->isIndirectCall()) {
                            //
                        }
                    }*/ else 
                        continue;
                    APInt ap_offset(64, 0, true);
                    auto basePointer = op->stripAndAccumulateConstantOffsets(*dlForInput, ap_offset, true);
                    auto offset = ap_offset.getSExtValue();
                    
                    llvm::Type *t = basePointer->getType();
                    if (t->isPointerTy())
                        t = t->getPointerElementType();
                    if (t->isStructTy()) {
                        if (t->getStructName() == basePointerStructName && offset>=input->offset) {
                            errs() << "find additonal use with offset " << offset << "\n";
                            errs() << (*I) << "\n";
                            auto dbg = I->getDebugLoc();
                            errs() << dbg->getFilename() << ":" << dbg->getLine() << "\n";
                            break;
                        }
                    }
                }
            }
        }

        string stripFileName(string fileName) {
            if (fileName.find("./") == 0) {
                return fileName.substr(2, fileName.size());
            }
            return fileName;
        }

        uint64_t getOffsetOfBaseObj(llvm::Instruction *I) {
            uint64_t ret = 0;
            GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(&(*I));
            APInt ap_offset(64, 0, true);
            bool success = GEP->accumulateConstantOffset(*dlForInput, ap_offset);
            assert(success);
            ret = ap_offset.getSExtValue();
            return ret;
        }

        uint64_t getSizeOfObj(llvm::Value *op) {
            uint64_t targetObjSize = -1;
            llvm::Type *t = op->getType();
            if (t->isPointerTy()) {
                llvm::Type *targetObjType = t->getPointerElementType();
                targetObjSize = dlForInput->getTypeAllocSize(targetObjType);
            }

            return targetObjSize;
        }

        void createObj4value(Value *v, Instruction* I, GlobalState * currState, std::vector<Instruction*> *pcallSites){
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
                ptinfo->targetObject->setAsTaintFieldSrc(loc, dl, true, 0);
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
        
        

    };


    char SAAPass::ID = 0;
    static RegisterPass<SAAPass> x("dr_checker", "Soundy Driver Checker", false, true);
}

