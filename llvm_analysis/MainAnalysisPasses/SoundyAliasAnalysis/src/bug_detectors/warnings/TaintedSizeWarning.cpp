//
// Created by machiry on 1/8/17.
//
#include "bug_detectors/warnings/TaintedSizeWarning.h"

using namespace llvm;

namespace DRCHECKER {

    void TaintedSizeWarning::printCompleteWarning(llvm::raw_ostream &O) const {
        O << "Non constant size used in copy_to(or from)_user function :" << this->found_by << "\n";
        O << "  at: ";
        InstructionUtils::printInst(this->target_instr,O);
        O << "  Call Context:";
        for(Instruction *currCallSite : this->callSiteTrace) {
            O << "   ";
            InstructionUtils::printInst(currCallSite);
        }
    }

    /*
    void TaintedSizeWarning::printWarning(llvm::raw_ostream &O) const {
        //this->warning_string.clear();
        //this->warning_string.append("Non constant size used in copy_to(or from)_user function");
        //this->warning_string = "Non constant size used in copy_to(or from)_user function";

        //VulnerabilityWarning::printWarning(O);
        O << "Non constant size used in copy_to(or from)_user function :" << this->found_by << "\n";
    */

}
