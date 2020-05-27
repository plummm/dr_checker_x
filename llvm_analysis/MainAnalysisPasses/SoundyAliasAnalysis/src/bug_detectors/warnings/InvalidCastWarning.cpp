//
// Created by machiry on 1/8/17.
//

#include <InstructionUtils.h>
#include "bug_detectors/warnings/InvalidCastWarning.h"

using namespace llvm;

namespace DRCHECKER {

    void InvalidCastWarning::printCompleteWarning(llvm::raw_ostream &O) const {
        O << "Trying to cast an object:";
        if(this->srcObjPtr != nullptr) {
            O << InstructionUtils::getValueStr(this->srcObjPtr);
        } else {
            O << " UNKNOWN OBJECT.";
        }
        O << " of size:";
        if(this->srcObjectSize != -1) {
            O << this->srcObjectSize;
        } else {
            O << " Unknown";
            if(this->srcSizeTainted) {
                O << " (Also TAINTED)";
            }

        }
        O << " to object of size:" << this->dstObjectSize;
        O << " :" << this->found_by << "\n";
        O << "  at: ";
        InstructionUtils::printInst(this->target_instr,O);
        O << "  Call Context:";
        for(Instruction *currCallSite : this->callSiteTrace) {
            O << "   ";
            InstructionUtils::printInst(currCallSite,O);
        }
    }

    void InvalidCastWarning::printWarning(llvm::raw_ostream &O) const {
        O << "\"warn_data\":{";
        O << "\"by\":\"";
        O << InstructionUtils::escapeJsonString(this->found_by);
        O << "\",";
        O << "\"warn_str\":\"";
        O << InstructionUtils::escapeJsonString("Trying to cast an object");
        O << "\",";
        O << "\"src_obj\":\"";
        if(this->srcObjPtr != nullptr) {
            O << InstructionUtils::escapeValueString(this->srcObjPtr);
        } else {
            O << InstructionUtils::escapeJsonString("UNKNOWN OBJECT");
        }
        O << "\",\"src_obj_size\":";
        if(this->srcObjectSize != -1) {
            O << this->srcObjectSize;
        } else {
            O << -1;
            if(this->srcSizeTainted) {
                O << ", \"src_obj_taint\":\"tainted\"";
            }

        }
        O << ",\"dst_obj_size\":";
        O << this->dstObjectSize << ",";
        //Location of the vulnerability site.
        InstructionUtils::printInstJson(this->target_instr,O);
        O << ",\"inst_trace\":";
        printInstlocTraceJson(&(this->trace),O);
        O << "}\n";
    }
}
