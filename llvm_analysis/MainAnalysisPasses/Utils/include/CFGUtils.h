//
// Created by machiry on 12/3/16.
//

#ifndef PROJECT_CFGUTILS_H
#define PROJECT_CFGUTILS_H
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "InstructionUtils.h"

using namespace llvm;
namespace DRCHECKER {
    /***
     *
     */
#define DEBUG_INTER_PROC_POSTDOM

    // This encodes the information to locate an instruction within a certain call context,
    // it also provides some utilities like reachability test w/ another instruction.
    class InstLoc {
        public:
        //The llvm inst itself.
        Value *inst;
        //The calling context of this inst.
        std::vector<Instruction*> *ctx;

        InstLoc(Value *inst, std::vector<Instruction*> *ctx) {
            this->inst = inst;
            this->ctx = ctx;
        }

        bool same(InstLoc *other) {
            if (!other) {
                return false;
            }
            //Compare the llvm inst itself.
            if (this->inst != other->inst) {
                return false;
            }
            //Compare the calling context of the inst.
            if (!this->ctx != !other->ctx) {
                return false;
            }
            //shortcut
            if (this->ctx == other->ctx) {
                return true;
            }
            if (this->ctx && *(this->ctx) != *(other->ctx)) {
                return false;
            }
            return true;
        }

        bool hasCtx() {
            return (this->ctx && !this->ctx->empty());
        }

        void print(raw_ostream &O);

        //Return true if this InstLoc post-dominates the "other" InstLoc.
        bool postDom(InstLoc *other);

        //Return true if this is reachable from the "other" InstLoc.
        bool reachable(InstLoc *other);
    };

    extern void printInstlocJson(InstLoc *inst, llvm::raw_ostream &O);

    extern void printInstlocTraceJson(std::vector<InstLoc*> *instTrace, llvm::raw_ostream &O);

    class BBTraversalHelper {
    public:
        /***
         * Get the Strongly connected components(SCC) of the CFG of the provided function in topological order
         * @param currF Function whose SCC visiting order needs to be fetched.
         * @return vector of vector of BasicBlocks.
         *     i.e vector of SCCs
         */
        static std::vector<std::vector<BasicBlock *> *> *getSCCTraversalOrder(Function &currF);

        //print the TraversalOrder to the output stream
        static void printSCCTraversalOrder(std::vector<std::vector<BasicBlock *>*> *order, raw_ostream *OS);

        /***
         * Get number of times all the BBs in the provided strongly connected component need to be analyzed
         * So that all the information is propagated correctly.
         * @param currSCC vector of BBs in the Strongly connected component.
         * @return number of times all the BBs needs to be analyzed to ensure
         * that all the information with in SCC is properly propogated.
         */
        static unsigned long getNumTimesToAnalyze(std::vector<BasicBlock *> *currSCC);

        /***
         * Checks whether a path exists from startInstr to endInstr along provided callSites.
         *
         * @param startInstr src or from instruction from where we need to check for path.
         * @param endInstr dst or to instruction to check for path
         * @param callSites pointer to the vector of callsites through which endInstr is reached from startInstr
         * @return true/false depending on whether a path exists or not.
         */
        static bool isReachable(Instruction *startInstr, Instruction *endInstr, std::vector<Instruction*> *callSites);

        static llvm::DominatorTree *getDomTree(llvm::Function*);

        //NOTE: as long as we have the post-dom tree, we can invoke its member function "->dominates()" to decide the
        //post-dominance relationship of two Insts:
        //Prototype from the llvm src file:
        /// Return true if \p I1 dominates \p I2. This checks if \p I2 comes before
        /// \p I1 if they belongs to the same basic block.
        /// bool dominates(const Instruction *I1, const Instruction *I2) const;
        static llvm::PostDominatorTree *getPostDomTree(llvm::Function*);

        //We assume src and end are within the same function.
        static bool instPostDom(Instruction *src, Instruction *end);
    };
}
#endif //PROJECT_CFGUTILS_H
