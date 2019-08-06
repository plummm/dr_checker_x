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


using namespace llvm;

namespace DRCHECKER {

//#define DEBUG_SCC_GRAPH
//#define DEBUG_TRAVERSAL_ORDER
//#define DEBUG_GLOBAL_VARIABLES
//#define DEBUG_GLOBAL_TAINT

#define NETDEV_IOCTL "NETDEVIOCTL"
#define READ_HDR "FileRead"
#define WRITE_HDR "FileWrite"
#define IOCTL_HDR "IOCTL"
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
                                       cl::init(0));

    static cl::opt<std::string> outputFile("outputFile",
                                            cl::desc("Path to the output file, where all the warnings should be stored."),
                                            cl::value_desc("Path of the output file."), cl::init(""));

    static cl::opt<std::string> instrWarnings("instrWarnOutput",
                                              cl::desc("Path to the output file, where all the warnings w.r.t instructions should be stored."),
                                              cl::value_desc("Path of the output file."), cl::init(""));


    struct SAAPass: public ModulePass {
    public:
        static char ID;
        //GlobalState moduleState;

        CallGraph *callgraph;
        FunctionChecker *currFuncChecker;

        SAAPass() : ModulePass(ID) {
            currFuncChecker = new KernelFunctionChecker();
        }

        ~SAAPass() {
            delete(currFuncChecker);
        }



        void getAllInterestingInitFunctions(Module &m, std::string currFuncName,
                                            std::set<Function*> interestingInitFuncs) {
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

            std::vector<Instruction *> callSites;
            FunctionChecker* targetChecker = new KernelFunctionChecker();
            // create data layout for the current module
            DataLayout *currDataLayout = new DataLayout(&m);

            RangeAnalysis::InterProceduralRA<RangeAnalysis::CropDFS> &range_analysis = getAnalysis<RangeAnalysis::InterProceduralRA<RangeAnalysis::CropDFS>>();
            GlobalState currState(&range_analysis, currDataLayout);
            // set the read and write flag in global state, to be used by differect detectors.
            currState.is_read_write_function = functionType == READ_HDR || functionType == WRITE_HDR;
            // set pointer to global state
            AliasAnalysisVisitor::callback->setPrivateData(&currState);
            // setting function checker(s).
            TaintAnalysisVisitor::functionChecker = targetChecker;
            AliasAnalysisVisitor::callback->targetChecker = targetChecker;

            // Setup aliases for global variables.
            setupGlobals(m);

            dbgs() << "Provided Function Type:" << functionType << ", Function Name:" << checkFunctionName << "\n";
            auto t_start = std::chrono::system_clock::now();
            dbgs() << "Anlysis starts at: ";
            this->printCurTime();
            // Call init functions.
            if(!skipInit) {
                std::set<Function*> toAnalyzeInitFunctions;
                getAllInterestingInitFunctions(m, checkFunctionName, toAnalyzeInitFunctions);
                dbgs() << "Analyzing:" << toAnalyzeInitFunctions.size() << " init functions\n";
                for(auto currInitFunc:toAnalyzeInitFunctions) {
                    dbgs() << "Analyzing init function:" << currInitFunc->getName() << "\n";
                    std::vector<std::vector<BasicBlock *> *> *traversalOrder =
                            BBTraversalHelper::getSCCTraversalOrder(*currInitFunc);

                    VisitorCallback *aliasVisitorCallback = new AliasAnalysisVisitor(currState, currInitFunc,
                                                                                     &callSites);

                    std::vector<VisitorCallback *> allCallBacks;
                    allCallBacks.insert(allCallBacks.end(), aliasVisitorCallback);

                    GlobalVisitor *vis = new GlobalVisitor(currState, currInitFunc, &callSites, traversalOrder,
                                                           allCallBacks);

                    vis->analyze();
                }
            }

            for(Module::iterator mi = m.begin(), ei = m.end(); mi != ei; mi++) {
                Function &currFunction = *mi;

                if(!currFunction.isDeclaration()) {
                    std::vector<std::vector<BasicBlock *> *> *traversalOrder = BBTraversalHelper::getSCCTraversalOrder(currFunction);
#ifdef DEBUG_TRAVERSAL_ORDER
                    if(currFunction.getName().str() == "n_tty_receive_char_special") {
                        std::cout << "Got Traversal order For:" << currFunction.getName().str() << "\n";
                        for (auto m1:*traversalOrder) {
                            std::cout << "SCC START:" << m1->size() << ":\n";
                            for (auto m2:*m1) {
                                std::cout << InstructionUtils::getBBStrID(m2) << " -> ";
                            }
                            std::cout << "SCC END\n";
                        }
                    }
                    continue;
#endif

#ifdef DEBUG_SCC_GRAPH
                    std::string Filename = "cfg_dot_files/cfg." + currFunction.getName().str() + ".dot";
                    errs() << "Writing '" << Filename << "'...";

                    std::error_code ErrorInfo;
                    raw_fd_ostream File(Filename, ErrorInfo, sys::fs::F_Text);

                    if (ErrorInfo.value() == 0)
                        WriteGraph(File, (const Function*)&currFunction);
                    else
                        errs() << "  error opening file for writing!";
                    errs() << "\n";
#endif

                    if(currFunction.getName().str() == checkFunctionName) {
                        // first instruction of the IOCTL function.
                        callSites.push_back(currFunction.getEntryBlock().getFirstNonPHIOrDbg());
                        // set up user function args.
                        setupFunctionArgs(&currFunction, currState, &callSites);
                        //hz: taint all global objects, field-sensitive.
                        addGlobalTaintSource(currState);

                        std::vector<VisitorCallback *> allCallBacks;

                        // add pre analysis bug detectors/
                        // these are the detectors, that need to be run before all the analysis passes.
                        //BugDetectorDriver::addPreAnalysisBugDetectors(currState, &currFunction, &callSites,
                        //                                              &allCallBacks, targetChecker);

                        // first add all analysis visitors.
                        addAllVisitorAnalysis(currState, &currFunction, &callSites, &allCallBacks);

                        // next, add all bug detector analysis visitors, which need to be run post analysis passed.
                        //BugDetectorDriver::addPostAnalysisBugDetectors(currState, &currFunction, &callSites,
                        //                                               &allCallBacks, targetChecker);

                        // create global visitor and run it.
                        GlobalVisitor *vis = new GlobalVisitor(currState, &currFunction, &callSites, traversalOrder, allCallBacks);

                        //vis->analyze();

                        //SAAVisitor *vis = new SAAVisitor(currState, &currFunction, &callSites, traversalOrder);
                        dbgs() << "Starting Analyzing function:" << currFunction.getName() << "\n";
                        vis->analyze();

                        auto t_now = std::chrono::system_clock::now();
                        std::chrono::duration<double> elapsed_seconds = t_now - t_start;
                        dbgs() << "Anlysis done in : " << elapsed_seconds.count() << "s\n";

                        dbgs() << "Now start to serialize the taint information...\n";
                        currState.serializeTaintInfo("taint_info_" + checkFunctionName + "_serialize");

                        auto t_end0 = std::chrono::system_clock::now();
                        elapsed_seconds = t_end0 - t_now;
                        dbgs() << "Taint info serialized in : " << elapsed_seconds.count() << "s\n";
                        
                        dbgs() << "Now start to dump the taint information...\n";
                        std::error_code EC;
                        llvm::raw_fd_ostream o_taint("taint_info_" + checkFunctionName, EC);
                        //Set a 5MB buffer to improve file I/O performance.
                        o_taint.SetBufferSize(5*1024*1024);
                        currState.dumpTaintInfo(o_taint);
                        o_taint.close();

                        //Write the taint info first to a in-mem string, then save it to the file, might be faster.
                        /*
                        std::string str_taint_inf;
                        llvm::raw_string_ostream o_taint(str_taint_inf);
                        currState.dumpTaintInfo(o_taint);
                        std::ofstream outfile;
                        outfile.open("taint_info_" + checkFunctionName);
                        outfile << o_taint.str();
                        outfile.close();
                        */

                        auto t_end1 = std::chrono::system_clock::now();
                        elapsed_seconds = t_end1 - t_end0;
                        dbgs() << "Taint info dumped in : " << elapsed_seconds.count() << "s\n";

                        /*
                        if(outputFile == "") {
                            // No file provided, write to dbgs()
                            dbgs() << "[+] Writing JSON output :\n";
                            dbgs() << "[+] JSON START:\n\n";
                            BugDetectorDriver::printAllWarnings(currState, dbgs());
                            BugDetectorDriver::printWarningsByInstr(currState, dbgs());
                            dbgs() << "\n\n[+] JSON END\n";
                        } else {
                            std::error_code res_code;
                            dbgs() << "[+] Writing output to:" << outputFile << "\n";
                            llvm::raw_fd_ostream op_stream(outputFile, res_code, llvm::sys::fs::F_Text);
                            BugDetectorDriver::printAllWarnings(currState, op_stream);
                            op_stream.close();

                            dbgs() << "[+] Return message from file write:" << res_code.message() << "\n";

                            std::string instrWarningsFile;
                            std::string originalFile = instrWarnings;
                            if(!originalFile.empty()) {
                                instrWarningsFile = originalFile;
                            } else {
                                instrWarningsFile = outputFile;
                                instrWarningsFile.append(".instr_warngs.json");
                            }

                            dbgs() << "[+] Writing Instr output to:" << instrWarningsFile << "\n";
                            llvm::raw_fd_ostream instr_op_stream(instrWarningsFile, res_code, llvm::sys::fs::F_Text);
                            BugDetectorDriver::printWarningsByInstr(currState, instr_op_stream);
                            instr_op_stream.close();

                            dbgs() << "[+] Return message from file write:" << res_code.message() << "\n";
                        }
                        */

                        //clean up
                        dbgs() << "Clean up GlobalVisitor at: ";
                        this->printCurTime();
                        delete(vis);

                        //((AliasAnalysisVisitor *)aliasVisitorCallback)->printAliasAnalysisResults(dbgs());
                    }
                }
            }
            // explicitly delete references to global variables.
            dbgs() << "Clean up global state at: ";
            this->printCurTime();
            currState.cleanup();
            // clean up.
            dbgs() << "Clean up DataLayout at: ";
            this->printCurTime();
            delete(currDataLayout);
            dbgs() << "All done: ";
            this->printCurTime();
        }

        void printCurTime() {
            auto t_now = std::chrono::system_clock::now();
            std::time_t now_time = std::chrono::system_clock::to_time_t(t_now);
            dbgs() << std::ctime(&now_time) << "\n";
        }

        void addAllVisitorAnalysis(GlobalState &targetState,
                                   Function *toAnalyze,
                                   std::vector<Instruction *> *srcCallSites,
                                   std::vector<VisitorCallback *> *allCallbacks) {

            // This function adds all analysis that need to be run by the global visitor.
            // it adds analysis in the correct order, i.e the order in which they need to be
            // run.

            VisitorCallback *currVisCallback = new AliasAnalysisVisitor(targetState, toAnalyze, srcCallSites);

            // first add AliasAnalysis, this is the main analysis needed by everyone.
            allCallbacks->insert(allCallbacks->end(), currVisCallback);

            currVisCallback = new TaintAnalysisVisitor(targetState, toAnalyze, srcCallSites);

            // next add taint analysis.
            allCallbacks->insert(allCallbacks->end(), currVisCallback);

            //hz: add the 3rd basic analysis: mod analysis to figure out which instructions can modify the global states.
            currVisCallback = new ModAnalysisVisitor(targetState, toAnalyze, srcCallSites);

            // next add mod analysis.
            allCallbacks->insert(allCallbacks->end(), currVisCallback);

            //hz: add the 4th basic analysis: switch analysis to figure out the mapping between "cmd" value and BBs in the ioctl().
            currVisCallback = new SwitchAnalysisVisitor(targetState, toAnalyze, srcCallSites);

            // next add mod analysis.
            allCallbacks->insert(allCallbacks->end(), currVisCallback);
        }

        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.setPreservesAll();
            AU.addRequired<RangeAnalysis::InterProceduralRA<RangeAnalysis::CropDFS>>();
            AU.addRequired<CallGraphWrapperPass>();
            AU.addRequired<LoopInfoWrapperPass>();
        }

    private:

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
            for(Module::global_iterator gstart = currGlobalList.begin(), gend = currGlobalList.end(); gstart != gend; gstart++) {
                // ignore constant immutable global pointers
                if((*gstart).isConstant()) {
                    continue;
                }
                GlobalState::addGlobalVariable(visitorCache, &(*gstart), globalObjectCache);
#ifdef DEBUG_GLOBAL_VARIABLES
                (*gstart).print(dbgs());
                    dbgs() << " NUM USES:" << (*gstart).getNumUses() << ", TYPE:";
                    (*gstart).getType()->print(dbgs());
                    //op1->print(dbgs());
                    dbgs() << "\n";

                dbgs() << "For:";
                dbgs() << (*gstart).getName() << ":";
                dbgs() << " of type (" << (*gstart).getType()->getContainedType(0)->isStructTy() << ","
                       << (*gstart).getType()->isPointerTy() << "," << (*gstart).getType()->isArrayTy() << "):";
                (*gstart).getType()->print(dbgs());
                dbgs() << ":";
                if((*gstart).hasInitializer()) {
                    Constant *initializationConst = (*gstart).getInitializer();
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

        void setupFunctionArgs(Function *targetFunction, GlobalState &targetState, std::vector<Instruction *> *callSites) {
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
            if(functionType == IOCTL_HDR) {
                // last argument is the user pointer.
                taintedArgs.insert(targetFunction->arg_size() - 1);
                // first argument is the file pointer
                pointerArgs.insert(0);
                is_handled = true;
            }
            //hz: We want to set all global variables as taint source,
            //for ioctl() in driver code, the FILE pointer should also
            //be regarded as a global variable.
            if(functionType.find(MY_IOCTL) == 0) {
                //Extract the user arg indices if any.
                std::vector<std::string> tks = split(functionType,"_");
                if (tks.size() > 2) {
                    for (int i = 2; i < tks.size(); ++i) {
                        //NOTE: Here may occur exception if the invalid arg is passed-in.
                        int idx = std::stoi(tks[i]);
                        dbgs() << "Set " << idx << "th arg of " << targetFunction->getName().str() << " as user arg (taint source)...\n";
                        taintedArgs.insert(idx);
                    }
                }else {
                    //by default the last argument is the user pointer.
                    taintedArgs.insert(targetFunction->arg_size() - 1);
                }
                is_handled = true;
            }
            if(functionType == READ_HDR || functionType == WRITE_HDR) {
                taintedArgs.insert(1);
                taintedArgs.insert(2);
                pointerArgs.insert(0);
                pointerArgs.insert(3);
                is_handled = true;
            }
            if(functionType == V4L2_IOCTL_FUNC) {
                taintedArgData.insert(targetFunction->arg_size() - 1);
                for(unsigned long i=0;i<targetFunction->arg_size(); i++) {
                    pointerArgs.insert(i);
                }
                is_handled = true;
            }
            if(functionType == DEVATTR_SHOW) {
                for(unsigned long i=0;i<targetFunction->arg_size(); i++) {
                    pointerArgs.insert(i);
                }
                is_handled = true;
            }
            if(functionType == DEVATTR_STORE) {
                if(targetFunction->arg_size() == 3) {
                    // this is driver attribute
                    taintedArgData.insert(1);
                } else {
                    // this is device attribute
                    taintedArgData.insert(2);
                }
                for (unsigned long i = 0; i < targetFunction->arg_size() - 1; i++) {
                    pointerArgs.insert(i);
                }
                is_handled = true;
            }
            if(functionType == NETDEV_IOCTL) {
                taintedArgData.insert(1);
                for(unsigned long i=0;i<targetFunction->arg_size()-1; i++) {
                    pointerArgs.insert(i);
                }
                is_handled = true;
            }
            //hz: the function doesn't have arguments. This is created for test purposes.
            if(functionType == NULL_ARG) {
                is_handled = true;
            }
            if(!is_handled) {
                dbgs() << "Invalid Function Type:" << functionType << "\n";
                dbgs() << "Errorring out\n";
            }
            assert(is_handled);


            std::map<Value *, std::set<PointerPointsTo*>*> *currPointsTo = targetState.getPointsToInfo(callSites);
            unsigned long arg_no=0;
            for(Function::arg_iterator arg_begin = targetFunction->arg_begin(), arg_end = targetFunction->arg_end(); arg_begin != arg_end; arg_begin++) {
                Value *currArgVal = &(*arg_begin);
                if(taintedArgs.find(arg_no) != taintedArgs.end()) {
                    //hz: Add a taint tag indicating that the taint is from user-provided arg, instead of global states.
                    //This tag represents the "arg", at the function entry its point-to object hasn't been created yet, so no "pobjs" for the tag.
                    TaintTag *currTag = new TaintTag(0,currArgVal,false);
                    TaintFlag *currFlag = new TaintFlag(currArgVal, true);
                    currFlag->setTag(currTag);
                    currFlag->instructionTrace.push_back(targetFunction->getEntryBlock().getFirstNonPHIOrDbg());
                    std::set<TaintFlag*> *currTaintInfo = new std::set<TaintFlag*>();
                    currTaintInfo->insert(currFlag);
                    TaintUtils::updateTaintInfo(targetState, callSites, currArgVal, currTaintInfo);
                }
                if(pointerArgs.find(arg_no) != pointerArgs.end()) {
                    AliasObject *obj = new FunctionArgument(currArgVal, currArgVal->getType(), targetFunction,
                                                            callSites);
                    PointerPointsTo *newPointsTo = new PointerPointsTo();
                    newPointsTo->targetPointer = currArgVal;
                    newPointsTo->fieldId = 0;
                    newPointsTo->dstfieldId = 0;
                    newPointsTo->targetObject = obj;
                    if(taintedArgData.find(arg_no) != taintedArgData.end()) {
                        TaintFlag *currFlag = new TaintFlag(currArgVal, true);
                        currFlag->instructionTrace.push_back(targetFunction->getEntryBlock().getFirstNonPHIOrDbg());
                        obj->taintAllFields(currFlag);
                    }
                    std::set<PointerPointsTo *> *newPointsToSet = new std::set<PointerPointsTo *>();
                    newPointsToSet->insert(newPointsToSet->end(), newPointsTo);
                    (*currPointsTo)[currArgVal] = newPointsToSet;
                } else {
                    assert(taintedArgData.find(arg_no) == taintedArgData.end());
                }
                arg_no++;

            }
        }

        //hz: try to set all global variables as taint source.
        void addGlobalTaintSource(GlobalState &targetState){
            //Type of globalVariables: std::map<Value *, std::set<PointerPointsTo*>*>
            for(auto const &it : GlobalState::globalVariables){
                Value *v = it.first;
                TaintFlag *currFlag = new TaintFlag(v, true);
                //Add a tag
                TaintTag *currTag = new TaintTag(0,v);
                currFlag->setTag(currTag);
                std::set<PointerPointsTo*> *ps = it.second;
                if (ps->size() <= 0) {
                    continue;
                }
                if (v->getType()){
                    Type *ty = v->getType();
                    if (ty->isPointerTy()){
                        ty = ty->getPointerElementType();
                    }
                    //Exclude certain types, e.g. function.
                    if (ty->isFunctionTy() || ty->isLabelTy() || ty->isMetadataTy()){
                        continue;
                    }
                }
                //Exclude the constants which cannot be modified.
                if (dyn_cast<ConstantData>(v) || dyn_cast<ConstantAggregate>(v)) {
                    continue;
                }
#ifdef DEBUG_GLOBAL_TAINT
                dbgs() << "addGlobalTaintSource(): Set the glob var as taint source: " << InstructionUtils::getValueStr(v) << "\n";
#endif
                for(auto const &p : *ps){
                    if (!p->targetObject) {
                        continue;
                    }
                    p->targetObject->taintAllFieldsWithTag(currFlag);
                    p->targetObject->is_taint_src = true;
#ifdef DEBUG_GLOBAL_TAINT
                    dbgs() << "addGlobalTaintSource(): Set the alias obj as taint source:\n";
                    dbgs() << "Object Type: " << InstructionUtils::getTypeStr(p->targetObject->targetType) << "\n";
                    dbgs() << " Object Ptr: " << InstructionUtils::getValueStr(p->targetObject->getObjectPtr()) << "\n";
#endif
                }
            }
        }

    };


    char SAAPass::ID = 0;
    static RegisterPass<SAAPass> x("dr_checker", "Soundy Driver Checker", false, true);
}

