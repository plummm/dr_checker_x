#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/CommandLine.h"


#include <string>
#include <unordered_map>
#include <unordered_set>
#include <iostream>
#include <fstream>
#include <stdio.h>
#include <vector>

using namespace llvm;
using namespace llvm::sys;
using namespace std;

class getRet{

public:
    set<BasicBlock *> visitedBB;
    Instruction* ret = nullptr;
    bool found = false;

    getRet(){}

    ~getRet(){}

    void BBvisit(BasicBlock* bb, int depth){   
        if(visitedBB.find(bb) != visitedBB.end() || found || depth > 20){
            return;
        }
        auto terminator = bb->getTerminator();
        if(isa<ReturnInst>(terminator)){
            ret = terminator;
            found = true;
        }
        if(isa<BranchInst>(terminator)){
            auto br = dyn_cast<BranchInst>(terminator);
            for(unsigned int i = 0; i < br->getNumSuccessors(); i++){
                auto successor = br->getSuccessor(i);
                BBvisit(successor, depth + 1);
            }
        }
    }
};


class getPath{

public:
    unordered_map<BasicBlock *, unordered_set<BasicBlock*>> BBChain;
    unsigned int ShortestPathSize = 99;
    std::vector<llvm::BasicBlock *> bbstack;
    std::vector<llvm::BasicBlock *> *ShortestPath = nullptr;

    getPath(){
        
    }

    ~getPath(){
        if(ShortestPath){
            delete ShortestPath;
        }
    }

    bool BBvisitor(BasicBlock* src, BasicBlock* dst, int depth){
        unordered_set<BasicBlock *> visitedBB;
        bool foundDst = false;
        if(depth == 20){
            return false;
        }
        if(visitedBB.find(src) != visitedBB.end()){
            return false;
        }
        visitedBB.insert(src);
        if(src == dst){
            return true;
        }
        auto terminator = src->getTerminator();
        if(isa<BranchInst>(terminator)){
            auto br = dyn_cast<BranchInst>(terminator);
            for(unsigned int i = 0; i < br->getNumSuccessors(); i++){
                auto successor = br->getSuccessor(i);
                if(BBChain.find(successor) != BBChain.end() || successor == dst){
                    foundDst = true;
                    BBChain[src].insert(successor);
                    continue;
                }
                if(BBvisitor(successor, dst, depth+1)){
                    foundDst = true;
                    BBChain[src].insert(successor);
                }
            }
        }
        return foundDst;

    }
    
    void DFSvisit(BasicBlock *src, BasicBlock *dst){
        bbstack.push_back(src);
        if(src == dst){
            if(bbstack.size() < ShortestPathSize){
                ShortestPathSize = bbstack.size();
                if(ShortestPath){
                    delete ShortestPath;
                }
                ShortestPath = new std::vector<llvm::BasicBlock *>();
                for(auto bb : bbstack){
                    ShortestPath->push_back(bb);
                }
            }
            bbstack.pop_back();
            return;
        }
        if(BBChain.find(src) != BBChain.end()){
            for(auto nextbb : BBChain[src]){
                if(find(bbstack.begin(), bbstack.end(), nextbb) == bbstack.end()){
                    DFSvisit(nextbb, dst);
                }
                    
            }
        }
        
        bbstack.pop_back();
    }

};