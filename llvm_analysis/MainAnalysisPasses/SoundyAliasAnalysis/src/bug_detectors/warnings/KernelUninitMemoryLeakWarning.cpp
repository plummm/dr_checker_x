//
// Created by machiry on 1/8/17.
//
#include <InstructionUtils.h>
#include "bug_detectors/warnings/KernelUninitMemoryLeakWarning.h"

using namespace llvm;

namespace DRCHECKER {

    void KernelUninitMemoryLeakWarning::printCompleteWarning(llvm::raw_ostream &O) const {
        O << "Potential Kernel Uninitialized Memory Leak detected by:" << this->found_by << "\n";
        O << "  at:";
        InstructionUtils::printInst(this->target_instr,O);
        O << "  Call Context:";
        for(Instruction *currCallSite : this->callSiteTrace) {
            O << "   ";
            InstructionUtils::printInst(currCallSite,O);
        }
        O << "  Leaked Structure: " << InstructionUtils::getValueStr(this->targetObj) << "\n";
    }

    void KernelUninitMemoryLeakWarning::printWarning(llvm::raw_ostream &O) const {
        O << "\"warn_data\":{";
        O << "\"by\":\"";
        O << InstructionUtils::escapeJsonString(this->found_by);
        O << "\",";
        O << "\"warn_str\":\"";
        O << InstructionUtils::escapeJsonString(this->warning_string);
        O << "\",";
        //
        InstructionUtils::printInstJson(this->target_instr,O);
        O << ",\"inst_trace\":";
        printInstlocTraceJson(&(this->trace),O);
        O << ",\"leaked_struct\":\"" << InstructionUtils::escapeValueString(this->targetObj) << "\"";
        O << "}\n";
    }
}
