#include "Universal.h"

using namespace llvm;
using namespace llvm::sys;
using namespace std;

static cl::opt<string> Calltrace_File ("CalltraceFile", cl::desc("The path of a calltrace"), cl::init(""));
static cl::opt<int> BUG_Offset ("Offset", cl::desc("Offset from base pointer that trigger OOB/UAF"), cl::init(0));
static cl::opt<int> BUG_Size ("Size", cl::desc("Size of vulnerable object"), cl::init(0));

static vector<CalltraceItem*> calltrace;
static int minDistance, tmpDistance;
static struct Input *head = NULL;
static Function *inlineCall = NULL;
static Module *TheModule = NULL;

struct Load {
    static bool isInst(Instruction *I) {
        if (LoadInst *load = dyn_cast<LoadInst>(I))
            return true;
        return false;
    }

    static void handleInst(LoadInst *load) {
        handleInst(load, NULL);
    }


    static void handleInst(LoadInst *load, Instruction *topCallsite) {
        llvm::Value *op = load->getPointerOperand();
        APInt ap_offset(64, 0, true);
        llvm::Value *basePointer = op->stripAndAccumulateConstantOffsets(*dlForInput, ap_offset, true);
        int64_t offset = ap_offset.getSExtValue();
        offset -= BUG_Offset;
        struct Input *ret = (struct Input *)malloc(sizeof(struct Input));
        //errs() << "basepointer: " << (*basePointer) << "\n";
        errs() << "Load: " << (*load) << " " << ret << "\n";
        minDistance = tmpDistance;
        ret->basePointer = basePointer;
        ret->inst = load;
        ret->offset = offset;
        ret->size = BUG_Size;
        ret->distance = minDistance;
        ret->topCallsite = topCallsite;
        ret->prev = NULL;
        ret->next = NULL;
        if (head == NULL) {
            head = (struct Input *)malloc(sizeof(struct Input));
            head->next = ret;
            ret->prev = head;
        } else {
             struct Input *next = head->next;
            next->prev = ret;
            ret->next = next;
            ret->prev = head;
            head ->next = ret;
        }
        errs() << "-----------------------------------\n";
        errs() << "offset to base obj is " << offset << "\n";
        errs() << "-----------------------------------\n";
    }

    static LoadInst *convertType(Instruction *I) {
        if (LoadInst *inst = dyn_cast<LoadInst>(&(*I)))
            return inst;
        return NULL;
    }

    static void printSloganHeader(Instruction *load) {
        errs() << "=============Inspect load instruction begin=============\n";
        //errs() << (*load) << "\n";
        errs() << "Found a Load instruction\n";
    }

    static void printSloganTail() {
        errs() << "=============Inspect load instruction end=============\n";
    }
};

struct Call {
    static bool isInst(Instruction *I) {
        if (CallInst *call = dyn_cast<CallInst>(I))
            return true;
        return false;
    }

    static void handleInst(CallInst *call) {
        Function *callee = call->getCalledFunction();
        if (!callee)
            return;
        inst_iterator I = inst_begin(*callee), E = inst_end(*callee);
        for (; I != E; ++I) {
            if (Load::isInst(&(*I))) {
                llvm::LoadInst *load = Load::convertType(&(*I));
                Load::handleInst(load, call);
            }
        }
        return;
    }

    static CallInst *convertType(Instruction *I) {
        if (CallInst *inst = dyn_cast<CallInst>(&(*I)))
            return inst;
        return NULL;
    }

    static void printSloganHeader(Instruction *call) {
        errs() << "=============Inspect call instruction begin=============\n";
        //errs() << (*call) << "\n";
        errs() << "Found a Call instruction\n";
    }

    static void printSloganTail() {
        errs() << "=============Inspect call instruction end=============\n";
    }
};