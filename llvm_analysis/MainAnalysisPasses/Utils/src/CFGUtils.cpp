//
// Created by machiry on 12/3/16.
//

#include "CFGUtils.h"

namespace DRCHECKER {

    // This code is copied from an online source.
    std::vector<std::vector<BasicBlock *> *>* BBTraversalHelper::getSCCTraversalOrder(Function &currF) {
        std::vector<std::vector<BasicBlock *> *> *bbTraversalList = new std::vector<std::vector<BasicBlock *> *>();
        const Function *F = &currF;
        for (scc_iterator<const Function *> I = scc_begin(F), IE = scc_end(F); I != IE; ++I) {
            // Obtain the vector of BBs in this SCC and print it out.
            const std::vector<const BasicBlock *> &SCCBBs = *I;
            std::vector<const BasicBlock *> *currSCC = new std::vector<const BasicBlock *>();
            for (std::vector<const BasicBlock *>::const_iterator BBI = SCCBBs.begin(),
                         BBIE = SCCBBs.end();
                 BBI != BBIE; ++BBI) {
                currSCC->insert(currSCC->begin(), (*BBI));
            }
            std::vector<BasicBlock *> *newCurrSCC = new std::vector<BasicBlock *>();
            for (unsigned int i = 0; i < currSCC->size(); i++) {
                for (Function::iterator b = currF.begin(), be = currF.end(); b != be; ++b) {
                    BasicBlock *BB = &(*b);
                    if (BB == (*currSCC)[i]) {
                        //newCurrSCC->insert(newCurrSCC->begin(), BB);
                        newCurrSCC->push_back(BB);
                        break;
                    }
                }
            }
            delete (currSCC);
            bbTraversalList->insert(bbTraversalList->begin(), newCurrSCC);
        }
        return bbTraversalList;
    }

    void BBTraversalHelper::printSCCTraversalOrder(std::vector<std::vector<BasicBlock *>*> *order, raw_ostream *OS) {
        if (!order || !OS) {
            return;
        }
        for (auto m1 : *order) {
            (*OS) << "SCC START:" << m1->size() << ":\n";
            for (auto m2 : *m1) {
                (*OS) << InstructionUtils::getBBStrID(m2) << " -> ";
            }
            (*OS) << "SCC END\n";
        }
    }

    unsigned long BBTraversalHelper::getNumTimesToAnalyze(std::vector<BasicBlock *> *currSCC) {
        /***
             * get number of times all the loop basicblocks should be analyzed.
             *  This is same as the longest use-def chain in the provided
             *  strongly connected component.
             *
             *  Why is this needed?
             *  This is needed because we want to ensure that all the
             *  information inside the loops have been processed.
             */

        std::map<BasicBlock *, unsigned long> useDefLength;
        useDefLength.clear();

        std::set<BasicBlock *> useDefChain;
        useDefChain.clear();
        std::set<BasicBlock *> visitedBBs;
        std::set<BasicBlock *> currBBToAnalyze;
        currBBToAnalyze.clear();
        unsigned long numToAnalyze = 1;

        for(BasicBlock *currBBMain:(*currSCC)) {
            if(useDefLength.find(currBBMain) == useDefLength.end()) {
                currBBToAnalyze.clear();
                currBBToAnalyze.insert(currBBToAnalyze.end(), currBBMain);
                useDefChain.clear();
                useDefChain.insert(useDefChain.end(), currBBMain);
                visitedBBs.clear();
                while (!currBBToAnalyze.empty()) {
                    for (auto currBB:currBBToAnalyze) {
                        visitedBBs.insert(visitedBBs.end(), currBB);
                        for (BasicBlock::iterator bstart = currBB->begin(), bend = currBB->end();
                             bstart != bend; bstart++) {
                            Instruction *currIns = &(*bstart);

                            for(int jkk=0;jkk < currIns->getNumOperands();jkk++) {
                                Value *i=currIns->getOperand(jkk);
                                if (Instruction *Inst = dyn_cast<Instruction>(i)) {
                                    BasicBlock *useBB = Inst->getParent();
                                    if (std::find(currSCC->begin(), currSCC->end(), useBB) != currSCC->end()) {
                                        if (useDefChain.find(useBB) == useDefChain.end()) {
                                            useDefChain.insert(useDefChain.end(), useBB);
                                        }
                                    }
                                }
                            }
                        }
                    }


                    currBBToAnalyze.clear();

                    for(auto b:useDefChain) {
                        if(visitedBBs.find(b) == visitedBBs.end()) {
                            currBBToAnalyze.insert(currBBToAnalyze.end(), b);
                        }
                    }

                }

                for (BasicBlock *vicBB:useDefChain) {
                    if(useDefLength.find(vicBB) == useDefLength.end()) {
                        useDefLength[vicBB] = useDefChain.size();
                    }
                }
            }
        }

        for(auto b:(*currSCC)) {
            if(useDefLength.find(b) != useDefLength.end()) {
                if(numToAnalyze < useDefLength[b]) {
                    numToAnalyze = useDefLength[b];
                }
            }
        }

        return numToAnalyze;

    }


    // following functions are shamelessly copied from LLVM.
    bool isPotentiallyReachableFromMany(SmallVectorImpl<BasicBlock *> &Worklist, BasicBlock *StopBB) {

        // Limit the number of blocks we visit. The goal is to avoid run-away compile
        // times on large CFGs without hampering sensible code. Arbitrarily chosen.
        unsigned Limit = 32;
        SmallSet<const BasicBlock*, 32> Visited;
        do {
            BasicBlock *BB = Worklist.pop_back_val();
            if (!Visited.insert(BB).second)
                continue;
            if (BB == StopBB)
                return true;

            if (!--Limit) {
                // We haven't been able to prove it one way or the other. Conservatively
                // answer true -- that there is potentially a path.
                return true;
            }
            Worklist.append(succ_begin(BB), succ_end(BB));
        } while (!Worklist.empty());

        // We have exhausted all possible paths and are certain that 'To' can not be
        // reached from 'From'.
        return false;
    }

    bool isPotentiallyReachable(const Instruction *A, const Instruction *B) {
        assert(A->getParent()->getParent() == B->getParent()->getParent() &&
               "This analysis is function-local!");

        SmallVector<BasicBlock*, 32> Worklist;

        if (A->getParent() == B->getParent()) {
            // The same block case is special because it's the only time we're looking
            // within a single block to see which instruction comes first. Once we
            // start looking at multiple blocks, the first instruction of the block is
            // reachable, so we only need to determine reachability between whole
            // blocks.
            BasicBlock *BB = const_cast<BasicBlock *>(A->getParent());

            // Linear scan, start at 'A', see whether we hit 'B' or the end first.
            for (BasicBlock::const_iterator I = A->getIterator(), E = BB->end(); I != E;
                 ++I) {
                if (&*I == B)
                    return true;
            }

            // Can't be in a loop if it's the entry block -- the entry block may not
            // have predecessors.
            if (BB == &BB->getParent()->getEntryBlock())
                return false;

            // Otherwise, continue doing the normal per-BB CFG walk.
            Worklist.append(succ_begin(BB), succ_end(BB));

            if (Worklist.empty()) {
                // We've proven that there's no path!
                return false;
            }
        } else {
            Worklist.push_back(const_cast<BasicBlock*>(A->getParent()));
        }

        if (A->getParent() == &A->getParent()->getParent()->getEntryBlock())
            return true;
        if (B->getParent() == &A->getParent()->getParent()->getEntryBlock())
            return false;

        return isPotentiallyReachableFromMany(
                Worklist, const_cast<BasicBlock *>(B->getParent()));
    }

    // llvm copying ends

    bool BBTraversalHelper::isReachable(Instruction *startInstr, Instruction *endInstr,
                                        std::vector<Instruction*> *callSites) {
        /***
         * Check if endInst is reachable from startInstr following the call sites
         * in the provided vector.
         */

        // both belong to the same function.
        if(startInstr->getParent()->getParent() == endInstr->getParent()->getParent()) {
            return isPotentiallyReachable(startInstr, endInstr);
        }

        // OK, both instructions belongs to different functions.
        // we need to find if startInstr can reach the
        // call instruction that resulted in invocation of the function of
        // endInstr
        assert(callSites->size() > 0 && "How can this be possible? we have 2 instructions, that belong to "
                                                "different functions, yet the call sites stack is empty");

        Instruction *newEndInstr;
        for(long i=(callSites->size() - 1);i>=0; i--) {
            newEndInstr = (*callSites)[i];
            if(newEndInstr->getParent()->getParent() == startInstr->getParent()->getParent()) {
                if(isPotentiallyReachable(startInstr, newEndInstr)) {
                    return true;
                }
            }
        }
        return false;

    }

    llvm::DominatorTree *BBTraversalHelper::getDomTree(llvm::Function* pfunc) { 
        //The mapping from one Func to its dominator tree;
        static std::map<llvm::Function*,llvm::DominatorTree*> domMap;
        if (!pfunc) {
            return nullptr;
        }
        if (domMap.find(pfunc) == domMap.end()) {
            llvm::DominatorTree *pdom = new llvm::DominatorTree(*pfunc);
            domMap[pfunc] = pdom;
        }
        return domMap[pfunc];
    }

    llvm::PostDominatorTree *BBTraversalHelper::getPostDomTree(llvm::Function* pfunc) { 
        //The mapping from one Func to its post-dominator tree;
        static std::map<llvm::Function*,llvm::PostDominatorTree*> postDomMap;
        if (!pfunc) {
            return nullptr;
        }
        if (postDomMap.find(pfunc) == postDomMap.end()) {
            llvm::PostDominatorTree *pdom = new llvm::PostDominatorTree(*pfunc);
            postDomMap[pfunc] = pdom;
        }
        return postDomMap[pfunc];
    }

    //Some code are borrowed from llvm 11.0, since lower version llvm may not have "dominates()" for two instructions. 
    bool BBTraversalHelper::instPostDom(Instruction *src, Instruction *end) {
        if (!end || !src || end->getFunction() != src->getFunction()) {
            return false;
        }
        BasicBlock *bsrc = src->getParent();
        BasicBlock *bend = end->getParent();
        if (bsrc != bend) {
            //
            Function *func = end->getFunction();
            llvm::PostDominatorTree *pdom = BBTraversalHelper::getPostDomTree(func);
            if (!pdom) {
                return false;
            }
            return pdom->dominates(bend,bsrc);
        }
        //Ok they are within the same BB, we simply look at their relative order.
        // PHINodes in a block are unordered.
        if (isa<PHINode>(src) && isa<PHINode>(end))
            return false;
        // Loop through the basic block until we find I1 or I2.
        BasicBlock::const_iterator I = bsrc->begin();
        for (; &*I != src && &*I != end; ++I);
        //If src comes before end in a same BB, then end post-dom src.
        return &*I == src;
    }

    void InstLoc::print(raw_ostream &O) {
        if (this->inst) {
            //First print the inst.
            if (dyn_cast<Instruction>(this->inst)) {
                InstructionUtils::printInst(dyn_cast<Instruction>(this->inst),O);
            }else {
                O << InstructionUtils::getValueStr(this->inst) << "\n";
            }
            //Then print the calling context by the function names.
            if (this->ctx && this->ctx->size() > 0) {
                O << "[";
                std::string lastFunc;
                for (Instruction *inst : *(this->ctx)) {
                    if (inst && inst->getFunction()) {
                        std::string func = inst->getFunction()->getName().str();
                        //TODO: self-recursive invocation
                        if (func != lastFunc) {
                            O << func << " -> ";
                            lastFunc = func;
                        }
                    }
                }
                O << "]\n";
            }
        }
    }

    //Different from the normal post-dom algorithm for two instructions within a same function, here we consider
    //the post-dom relationship for two InstLoc (i.e. instructions plus their full calling contexts), so if InstLoc A
    //post-dom InstLoc B, that means all execution flows from InstLoc B will eventually reach InstLoc A w/ its specific
    //calling contexts.
    bool InstLoc::postDom(InstLoc *other) {
        if (!other) {
            return false;
        }
        //(1) First identify the common prefix of the calling contexts, if none, then obviously no post-dom relationship,
        //if any, then the question is converted to "whether this inst post-dom the call site of 'other' in the common prefix".
        if (!this->hasCtx()) {
            //This means current InstLoc is outside of any functions (e.g. a preset global variable), so no way it can post-dominate "other".
            return false;
        }
        int ip = 0;
        if (other->hasCtx()) {
            //Both "this" and "other" has some contexts.
            //NOTE 1: the structure of the calling context is "entry inst -> call site -> entry inst -> call site -> ...", so odd ctx index indicates
            //a call inst.
            //NOTE 2: the total size of a calling context must be odd. (i.e. it must end w/ the entry inst of the callee).
            assert(this->ctx->size() % 2);
            assert(other->ctx->size() % 2);
            while (ip < this->ctx->size() && ip < other->ctx->size() && (*(this->ctx))[ip] == (*(other->ctx))[ip] && ++ip);
            if (ip == 0) {
                //Both have calling contexts but no common prefix... This means the top-level entry functions are different, no way to post-dom.
                return false;
            }
            //The two calling contexts diverges at a certain point, here we have different situations:
            //1. They diverge within a same caller.
            //1.1. "this" takes callee A while "other" takes callee B.
            //1.2. "this" is just a normal inst within the caller and "other" takes callee B.
            //1.3. "this" takes callee A while "other" is a normal inst
            //1.4. both are normal inst
            //For 1. we need to first see whether "this" post-doms "other" within the common caller, if not return false immediately, otherwise
            //we need to further inspect the remaining part of "this" calling context to see whether it *must* end w/ this->inst.
            //2. They diverge at a same call site and take different callees (e.g. an indirect call), in this case "this" cannot post-dom "other".
            if (ip >= this->ctx->size()) {
                //This must be case 1.2. or 1.4., since there are no further context for "this", no need for further inspect.
                Instruction *end = dyn_cast<Instruction>(this->inst);
                Instruction *src = dyn_cast<Instruction>(other->inst);
                if (ip < other->ctx->size()) {
                    src = (*(other->ctx))[ip];
                }
                if (!end || !src || end->getFunction() != src->getFunction()) {
                    //Is this possible?
#ifdef DEBUG_INTER_PROC_POSTDOM
                    dbgs() << "InstLoc::postDom(): !end || !src || end->getFunction() != src->getFunction() - 0\n"; 
#endif
                    return false;
                }
                return BBTraversalHelper::instPostDom(src,end);
            }
            if (ip >= other->ctx->size()) {
                //This must be case 1.3. We may still need to inspect the remaining "this" context.
                Instruction *src = dyn_cast<Instruction>(other->inst);
                Instruction *end = dyn_cast<Instruction>((*(this->ctx))[ip]);
                if (!end || !src || end->getFunction() != src->getFunction()) {
                    //Is this possible?
#ifdef DEBUG_INTER_PROC_POSTDOM
                    dbgs() << "InstLoc::postDom(): !end || !src || end->getFunction() != src->getFunction() - 1\n"; 
#endif
                    return false;
                }
                if (!BBTraversalHelper::instPostDom(src,end)) {
                    return false;
                }
            }else {
                //Ok, the common prefix are well contained in both contexts, it may be case 1.1. or 2., we can differentiate them by index oddness. 
                if (ip % 2) {
                    //case 2, return false directly.
                    return false;
                }
                //case 1.1., we may still need further inspect.
                if (!BBTraversalHelper::instPostDom((*(other->ctx))[ip],(*(this->ctx))[ip])) {
                    return false;
                }
            }
            ++ip;
        }
        //(2) Then we need to decide the post-dom relationship between the caller entrance and callee invocation site of each function
        //in the remaining calling context (beside the common prefix) of "this".
        //NOTE: at this point "ip" must be the index of an entry inst in "this" calling context.
        assert(!(ip % 2));
        assert(ip < this->ctx->size());
        while (ip + 1 < this->ctx->size()) {
            if (!BBTraversalHelper::instPostDom((*(this->ctx))[ip],(*(this->ctx))[ip+1])) {
                return false;
            }
            ++ip;
        }
        Instruction *end = dyn_cast<Instruction>(this->inst);
        if (end && !BBTraversalHelper::instPostDom((*(this->ctx))[ip],end)) {
            return false;
        }
        return true;
    }

}
