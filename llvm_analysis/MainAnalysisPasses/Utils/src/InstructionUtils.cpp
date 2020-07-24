//
// Created by machiry on 12/5/16.
//

#include <set>
#include <llvm/IR/CFG.h>
#include "InstructionUtils.h"

using namespace llvm;

//#define DEBUG_TYPE_CMP

namespace DRCHECKER {

#define DEBUG_IS_ASAN_INST
//#define DEBUG_GET_TY_DESC
#define DEBUG_RELATE_TYPE_NAME

    bool InstructionUtils::isPointerInstruction(Instruction *I) {
        bool retVal = false;
        LoadInst *LI = dyn_cast<LoadInst>(I);
        if(LI) {
            retVal = true;
        }
        StoreInst *SI = dyn_cast<StoreInst>(I);
        if(SI) {
            retVal = true;
        }
        VAArgInst *VAAI = dyn_cast<VAArgInst>(I);
        if(VAAI) {
            retVal = true;
        }
        return retVal;
    }

    std::string InstructionUtils::getInstructionName(Instruction *I) {
        if(I->hasName()) {
            return I->getName().str();
        } else {
            return "N/A";
        }
    }

    std::string InstructionUtils::getValueName(Value *v) {
        if(v->hasName()) {
            return v->getName().str();
        } else {
            return "No Name";
        }
    }

    std::string InstructionUtils::escapeJsonString(const std::string& input) {
        std::ostringstream ss;
        for (auto iter = input.cbegin(); iter != input.cend(); iter++) {
            switch (*iter) {
                case '\\':
                    ss << "\\\\";
                    break;
                case '"':
                    ss << "\\\"";
                    break;
                case '/':
                    ss << "\\/";
                    break;
                case '\b':
                    ss << "\\b";
                    break;
                case '\f':
                    ss << "\\f";
                    break;
                case '\n':
                    ss << "\\n";
                    break;
                case '\r':
                    ss << "\\r";
                    break;
                case '\t':
                    ss << "\\t";
                    break;
                default:
                    ss << *iter;
                    break;
            }
        }
        return ss.str();
    }

    std::string InstructionUtils::escapeValueString(Value *currInstr) {
        return InstructionUtils::escapeJsonString(InstructionUtils::getValueStr(currInstr));
    }

    DILocation* getRecursiveDILoc(Instruction *currInst, std::string &funcFileName, std::set<BasicBlock*> &visitedBBs) {
        DILocation *currIL = currInst->getDebugLoc().get();
        if(funcFileName.length() == 0) {
            return currIL;
        }
        if(currIL != nullptr && currIL->getFilename().equals(funcFileName)) {
            return currIL;
        }

        BasicBlock *currBB = currInst->getParent();
        if(visitedBBs.find(currBB) != visitedBBs.end()) {
            return nullptr;
        }
        for(auto &iu :currBB->getInstList()) {
            Instruction *currIterI = &iu;
            DILocation *currIteDL = currIterI->getDebugLoc();
            if(currIteDL != nullptr && currIteDL->getFilename().equals(funcFileName)) {
                return currIteDL;
            }
            if(currIterI == currInst) {
                break;
            }
        }

        visitedBBs.insert(currBB);


        for (auto it = pred_begin(currBB), et = pred_end(currBB); it != et; ++it) {
            BasicBlock* predecessor = *it;
            DILocation *currBBLoc = getRecursiveDILoc(predecessor->getTerminator(), funcFileName, visitedBBs);
            if(currBBLoc != nullptr) {
                return currBBLoc;
            }
        }
        return nullptr;
    }

    std::string getFunctionFileName(Function *F) {
        SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
        F->getAllMetadata(MDs);
        for (auto &MD : MDs) {
            if (MDNode *N = MD.second) {
                if (auto *subProgram = dyn_cast<DISubprogram>(N)) {
                    return subProgram->getFilename();
                }
            }
        }
        return "";
    }


    DILocation* InstructionUtils::getCorrectInstrLocation(Instruction *I) {
        DILocation *instrLoc = I->getDebugLoc().get();
        //BasicBlock *firstBB = &(I->getFunction()->getEntryBlock());
        //Instruction *firstInstr = firstBB->getFirstNonPHIOrDbg();

        //DILocation *firstIL = firstInstr->getDebugLoc().get();
        std::set<BasicBlock*> visitedBBs;
        std::string funcFileName = getFunctionFileName(I->getFunction());


        if(instrLoc != nullptr && instrLoc->getFilename().endswith(".c")) {
            return instrLoc;
        }

        if(instrLoc == nullptr || (funcFileName.length() > 0  && !instrLoc->getFilename().equals(funcFileName))) {
            // OK, the instruction is from the inlined function.
            visitedBBs.clear();
            DILocation *actualLoc = getRecursiveDILoc(I, funcFileName, visitedBBs);
            if(actualLoc != nullptr) {

                return actualLoc;
            }
        }

        return instrLoc;
    }

    //hz: my feeling is that above "getCorrectInstrLocation" is unnecessarily complex and there should be better solution
    //to get the correct DILocation just for the real inline site (instead of inside the original callee definition).
    DILocation* InstructionUtils::getCorrectInstLoc(Instruction *I) {
        if (!I) {
            return nullptr;
        }
        DILocation *dloc = I->getDebugLoc().get();
        //Deal w/ a special case here: sometimes the first instruction in a function is an "alloc", which usually doesn't
        //have a DILocation associated, but on the other hand, we only want to use it to locate the function start (e.g.
        //in the calling context), so in this situation we can use the first instruction in the same entry BB who has the DILocation instead.
        if (!dloc) {
            if (I->getParent() && I->getFunction()) {
                BasicBlock &firstBB = I->getFunction()->getEntryBlock();
                if (firstBB.getFirstNonPHIOrDbg() == I) {
                    for (Instruction &inst : firstBB) {
                        dloc = inst.getDebugLoc().get();
                        if (dloc) {
                            break; 
                        }
                    }
                }
            }
        }
        while (dloc) {
            MDNode *md = dloc->getInlinedAt();
            if (!md) {
                //This means we have reached the bottom.
                break;
            }
            if (dyn_cast<DILocation>(md)) {
                dloc = dyn_cast<DILocation>(md);
            }else {
                //Not sure whether this is possible...
                dbgs() << "!!! InstructionUtils::getCorrectInstLoc(): The inlinedAt metadata is not a DILocation! inst: "
                << InstructionUtils::getValueStr(I) << "\n";
                break;
            }
        }
        return dloc;
    }

    int getCorrectLineNumber(DILocation *d) {
        if (!d) {
            return -1;
        }
        int l = d->getLine();
        if (l == 0) {
            //It's very unlikely that the instr is at line 0...
            //Let's try to find the real line number from the "scope".
            MDNode *n = d->getScope();
            if (n) {
                if (dyn_cast<DILexicalBlock>(n)) {
                    return dyn_cast<DILexicalBlock>(n)->getLine();
                }
                if (dyn_cast<DISubprogram>(n)) {
                    return dyn_cast<DISubprogram>(n)->getLine();
                }
            }
        }
        return l;
    }

    int InstructionUtils::getInstrLineNumber(Instruction *I) {
        DILocation *targetLoc = InstructionUtils::getCorrectInstLoc(I);
        return getCorrectLineNumber(targetLoc);
    }

    void InstructionUtils::printInst(Instruction *I, raw_ostream &ROS) {
        static std::map<Instruction*,std::string> InstPrintMap;
        if (!I){
            return;
        }
        if (InstPrintMap.find(I) != InstPrintMap.end()){
            ROS << InstPrintMap[I];
            return;
        }
        std::string str;
        llvm::raw_string_ostream OS(str);
        //Inst, BB, Function, and File
        std::string& inst = InstructionUtils::getValueStr(dyn_cast<Value>(I));
        OS << inst  << "/" << InstructionUtils::getInstStrID_No(I) << " ,BB: ";
        if (I->getParent()) {
            OS << InstructionUtils::getBBStrID(I->getParent()) << "/" << InstructionUtils::getBBStrID_No(I->getParent());
        }
        OS << " ,FUNC: ";
        if (I->getFunction()) {
            OS << I->getFunction()->getName().str();
        }
        OS << " ,SRC: ";
        DILocation *instrLoc = InstructionUtils::getCorrectInstLoc(I);
        if (instrLoc != nullptr) {
            OS << InstructionUtils::escapeJsonString(instrLoc->getFilename());
            OS << " @ " << getCorrectLineNumber(instrLoc);
        } else {
            OS << "N/A";
        }
        OS << "\n";
        InstPrintMap[I] = OS.str();
        ROS << OS.str();
    }

    void InstructionUtils::printInstJson(Instruction *I, raw_ostream &OS) {
        static std::map<Instruction*,std::string> InstPrintJsonMap;
        if (!I){
            return;
        }
        if (InstPrintJsonMap.find(I) != InstPrintJsonMap.end()) {
            OS << InstPrintJsonMap[I];
            return;
        }
        std::string str;
        llvm::raw_string_ostream O(str);
        //
        O << "\"instr\":\"";
        O << InstructionUtils::escapeValueString(I) << "\",";
        O << "\"at_line\":";
        DILocation *instrLoc = InstructionUtils::getCorrectInstLoc(I);
        if(instrLoc != nullptr) {
            O << getCorrectLineNumber(instrLoc) << ",\"at_file\":\"" << InstructionUtils::escapeJsonString(instrLoc->getFilename()) << "\",";
        } else {
            O << "-1,";
        }
        O << "\"at_func\":";
        if (I->getFunction()) {
            O << "\"" << InstructionUtils::escapeJsonString(I->getFunction()->getName()) << "\"";
        }else {
            O << "-1";
        }
        //NOTE: we will not output a newline here, giving the caller some flexibilities.
        InstPrintJsonMap[I] = O.str();
        OS << O.str();
    }

    void InstructionUtils::stripFuncNameSuffix(std::string *fn) {
        if (!fn) {
            return;
        }
        std::size_t n = fn->rfind(".");
        if (n != std::string::npos) {
            fn->erase(n);
        }
        return;
    }

    LOC_INF* InstructionUtils::getInstStrRep(Instruction *I) {
        if(!I){
            return nullptr;
        }
        std::string inst,bb,func,mod;
        DILocation *instrLoc = InstructionUtils::getCorrectInstLoc(I);
        inst = InstructionUtils::getInstStrID_No(I);
        if(I->getParent()){
			bb = InstructionUtils::getBBStrID_No(I->getParent());
        }
        if(I->getFunction()){
            func = I->getFunction()->getName().str();
            InstructionUtils::stripFuncNameSuffix(&func);
        }
        //Put the file name.
        if (instrLoc != nullptr) {
            mod = instrLoc->getFilename();
        } else {
            if(I->getModule()){
                mod = I->getModule()->getName().str();
            }else{
                //Is this possible?
            }
        }
        LOC_INF *str_inst = new LOC_INF;
        str_inst->push_back(inst);
        str_inst->push_back(bb);
        str_inst->push_back(func);
        str_inst->push_back(mod);
        return str_inst;
    }

    std::vector<LOC_INF>* InstructionUtils::getStrCtx(std::vector<Instruction*> *callSites) {
        std::vector<LOC_INF> *pvec = new std::vector<LOC_INF>();
        for(Instruction *currCallSite : *callSites) {
            LOC_INF *str_inst = InstructionUtils::getInstStrRep(currCallSite);
            if(str_inst){
                pvec->push_back(*str_inst);
            }
        }
        return pvec;
    }

    std::string& InstructionUtils::getBBStrID(BasicBlock* B) {
        static std::map<BasicBlock*,std::string> BBNameMap;
        if (BBNameMap.find(B) == BBNameMap.end()) {
            if (B) {
                if (!B->getName().empty()){
                    BBNameMap[B] = B->getName().str();
                }else{
    	            std::string Str;
    	            raw_string_ostream OS(Str);
    	            B->printAsOperand(OS, false);
                    BBNameMap[B] = OS.str();
                }
            }else{
                BBNameMap[B] = "";
            }
        }
        return BBNameMap[B];
    }

    std::string& InstructionUtils::getBBStrID_No(BasicBlock* B) {
        static std::map<BasicBlock*,std::string> BBNameNoMap;
        if (BBNameNoMap.find(B) == BBNameNoMap.end()) {
            if (B) {
                if (!B->getName().empty()){
                    BBNameNoMap[B] = B->getName().str();
                }else if (B->getParent()){
                    int no = 0;
                    for (BasicBlock& bb : *(B->getParent())) {
                        if (&bb == B) {
                            BBNameNoMap[B] = std::to_string(no);
                            break;
                        }
                        ++no;
                    }
                }else{
                    //Seems impossible..
                    BBNameNoMap[B] = "";
                }
            }else{
                BBNameNoMap[B] = "";
            }
        }
        return BBNameNoMap[B];
    }

    std::string& InstructionUtils::getInstStrID_No(Instruction* I) {
        static std::map<Instruction*,std::string> InstNameNoMap;
        if (InstNameNoMap.find(I) == InstNameNoMap.end()) {
            if (I) {
                if (false){
                //if (!I->getName().empty()){
                    InstNameNoMap[I] = I->getName().str();
                }else if (I->getParent()){
                    int no = 0;
                    for (Instruction& i : *(I->getParent())) {
                        if (&i == I) {
                            InstNameNoMap[I] = std::to_string(no);
                            break;
                        }
                        ++no;
                    }
                }else{
                    //Seems impossible..
                    InstNameNoMap[I] = "";
                }
            }else{
                InstNameNoMap[I] = "";
            }
        }
        return InstNameNoMap[I];
    }

    //Set up a cache for the expensive "print" operation.
    std::string& InstructionUtils::getValueStr(Value *v) {
        static std::map<Value*,std::string> ValueNameMap;
        if (ValueNameMap.find(v) == ValueNameMap.end()) {
            if(v){
                std::string str;
                llvm::raw_string_ostream ss(str);
                ss << *v;
                ValueNameMap[v] = ss.str();
            }else{
                ValueNameMap[v] = "";
            }
        }
        return ValueNameMap[v];
    }

    //Set up a cache for the expensive "print" operation specifically for Type.
    std::string& InstructionUtils::getTypeStr(Type *v) {
        static std::map<Type*,std::string> TypeNameMap;
        if (TypeNameMap.find(v) == TypeNameMap.end()) {
            if(v){
                std::string str;
                llvm::raw_string_ostream ss(str);
                ss << *v;
                TypeNameMap[v] = ss.str();
            }else{
                TypeNameMap[v] = "";
            }
        }
        return TypeNameMap[v];
    }

    //hz: whether it's a scalar value.
    //Although kernel doesn't use float numbers, we still consider it since we may extend Dr.Checker for general programs later.
    bool InstructionUtils::isScalar(Value* v) {
        if (!v) {
            return false;
        }
        Type *ty = v->getType();
        if (!ty) {
            return false;
        }
        if (ty->isIntegerTy() || ty->isFloatingPointTy()) {
            return true;
        }
        return false;
    }

    int InstructionUtils::getConstantValue(Constant* C, TRAIT* res) {
        if (!C || !res) {
            return 0;
        }
        if (dyn_cast<llvm::ConstantInt>(C)) {
            (*res)["CONST_INT"] = (dyn_cast<llvm::ConstantInt>(C))->getSExtValue();
            return 1;
        }else if (dyn_cast<llvm::ConstantFP>(C)) {
            //TODO: we need to put the float value in an "int64_t"
            (*res)["CONST_FP"] = 0;
            return 2;
        }else if (dyn_cast<llvm::UndefValue>(C)) {
            (*res)["CONST_UNDEF"] = 0;
            return 3;
        }else if (dyn_cast<llvm::ConstantExpr>(C)) {
            //TODO: we need to evaluate the expr to a numeric value, how to do that?
            (*res)["CONST_EXPR"] = 0;
            return 4;
        }else if (dyn_cast<llvm::ConstantPointerNull>(C)) {
            (*res)["CONST_NULLPTR"] = 0;
            return 5;
        }else if (dyn_cast<llvm::ConstantTokenNone>(C)) {
            (*res)["CONST_NONETK"] = 0;
            return 6;
        }else {
            //Ignore other cases for now.
            (*res)["CONST_OTHER"] = 0;
            return 7;
        }
    }

    Value* InstructionUtils::stripAllCasts(Value* v, bool for_scalar) {
        while (v) {
            if (dyn_cast<llvm::CastInst>(v)) {
                v = (dyn_cast<llvm::CastInst>(v))->getOperand(0);
                continue;
            }
            if (dyn_cast<llvm::BitCastOperator>(v)) {
                v = (dyn_cast<llvm::BitCastOperator>(v))->getOperand(0);
                continue;
            }
            if (dyn_cast<llvm::PtrToIntOperator>(v)) {
                if (for_scalar) {
                    //This means it's not a real scalar, but just converted from a pointer, we may ignore this case.
                    return nullptr;
                }else {
                    v = (dyn_cast<llvm::PtrToIntOperator>(v))->getOperand(0);
                    continue;
                }
            }
            if (dyn_cast<llvm::ZExtOperator>(v)) {
                v = (dyn_cast<llvm::ZExtOperator>(v))->getOperand(0);
                continue;
            }
            //It's currently not a cast inst.
            break;
        }
        return v;
    }

    std::string InstructionUtils::getCalleeName(CallInst* I, bool strip) {
        if (!I) {
            return "";
        }
        Function *callee = I->getCalledFunction();
        if (callee) {
            std::string n = callee->getName().str();
            if (strip) {
                InstructionUtils::stripFuncNameSuffix(&n);
            }
            return n;
        }
        return "";
    }

    std::set<uint64_t> *InstructionUtils::getCmdValues(std::vector<Instruction*> *ctx, Instruction* inst, std::map<BasicBlock*,std::set<uint64_t>> *switchMap) {
        if ((!switchMap) || switchMap->empty()) {
            return nullptr;
        }
        BasicBlock *entry_bb = nullptr;
        if (inst) {
            entry_bb = inst->getParent();
        }
        //NOTE: The very first instruction in the context is the same across all contexts (i.e. the first inst in the entry func)
        //So the below loop will not consider lookup the 1st instruction in the SwitchMap.
        if (ctx) {
            //We should find the latest call site which has the associated switch-case info.
            for (int i = ctx->size()-1; i >= 0; --i) {
                if(entry_bb && switchMap->find(entry_bb) != switchMap->end()){
                    return &((*switchMap)[entry_bb]);
                }
                if ((*ctx)[i]) {
                    //dbgs() << "((*ctx)[i])->getParent()\n";
                    //dbgs() << i << " | " << *((*ctx)[i]) << "\n";
                    entry_bb = ((*ctx)[i])->getParent();
                }else {
                    //
                }
            }
        }
        return nullptr;
    }

    void InstructionUtils::trim_num_suffix(std::string *s) {
        if (!s) {
            return;
        }
        size_t nd = s->rfind("."), t = 0;
        if (nd != std::string::npos) {
            std::string suffix = s->substr(nd+1);
            try {
                std::stoi(suffix,&t,10);
            }catch(...) {
                t = 0;
            }
            if (t >= suffix.size()) {
                //This means the whole suffix can be converted to an integer, thus a numeric suffix.
                s->erase(nd);
            }
        }
        return;
    }

    std::string InstructionUtils::trim_struct_name(std::string &s) {
        std::string r;
        //Strip the name prefix
        if (s.find("struct.") == 0) {
            r = s.substr(7);
        }
        //Strip the numeric suffix.
        InstructionUtils::trim_num_suffix(&r);
        return r;
    }

    //E.g. i8** -> 2, i8* -> 1, i8 -> 0
    //The base type will be returned to "bty" if provided.
    int InstructionUtils::getPtrLayer(Type *ty, Type **bty = nullptr) {
        int r = 0;
        while (ty) {
            if (ty->isPointerTy()) {
                ++r;
                ty = ty->getPointerElementType();
            }else {
                break;
            }
        }
        if (bty) {
            *bty = ty;
        }
        return r;
    }

    //In theory, we can simply compare two Type by "==" in llvm,
    //but sometimes we want to handle cases like "%struct.A" and "%struct.A.123", 
    //they are basically the same but llvm does assign different Type for them.
    bool InstructionUtils::same_types(Type* ty0, Type* ty1, bool wild_intp) {
        if (ty0 == ty1) {
            return true;
        }
        if (!ty0 != !ty1) {
            return false;
        }
        if (wild_intp) {
            //i8/void can match any non-composite types, but if the other is composite, we return false.
            if (InstructionUtils::isPrimitiveTy(ty0,8) || InstructionUtils::isPrimitiveTy(ty1,8)) {
                return (!dyn_cast<CompositeType>(ty0) && !dyn_cast<CompositeType>(ty1));
            }
        }
        //From now on neither can be null.
        if (ty0->getTypeID() != ty1->getTypeID()) {
            //This means their basic types are different, e.g. a pointer vs an integer.
            return false;
        }
        unsigned n = ty0->getNumContainedTypes();
        if (n != ty1->getNumContainedTypes()) {
            return false;
        }
        Type *bty0 = nullptr, *bty1 = nullptr;
        int l0 = InstructionUtils::getPtrLayer(ty0,&bty0);
        int l1 = InstructionUtils::getPtrLayer(ty1,&bty1);
        if (l0 != l1) {
            return false;
        }
        if (l0 > 0) {
            //Both are pointers w/ the same layers, we compare their base types.
            return InstructionUtils::same_types(bty0,bty1,wild_intp);
        }
        //From now on both types are not pointers, and they have the same type ID:
        //https://llvm.org/doxygen/classllvm_1_1Type.html#a5e9e1c0dd93557be1b4ad72860f3cbda
        if (!dyn_cast<CompositeType>(ty0)) {
            return (ty0 == ty1);
        }else if (ty0->isStructTy()) {
            //Compare two struct types by their names (w/ numeric suffix trimmed).
            StructType *st0 = dyn_cast<StructType>(ty0);
            StructType *st1 = dyn_cast<StructType>(ty1);
            if (st0 && st1 && st0->hasName() && st1->hasName()) {
                std::string n0 = st0->getName().str();
                std::string n1 = st1->getName().str();
                //For anonymized structs, we still need to count the numeric suffix.
                if (n0.find(".anon.") != std::string::npos && n1.find(".anon.") != std::string::npos) {
                    return (n0 == n1);
                }
                //trim the numeric suffix if any.
                InstructionUtils::trim_num_suffix(&n0);
                InstructionUtils::trim_num_suffix(&n1);
#ifdef DEBUG_TYPE_CMP
                dbgs() << "InstructionUtils::same_types(): cmp struct (suffix): " << (n0==n1) << "\n";
#endif
                return (n0 == n1); 
            }else {
#ifdef DEBUG_TYPE_CMP
                dbgs() << "InstructionUtils::same_types(): cmp struct (no name)\n";
#endif
                return false;
            }
        }else if (dyn_cast<SequentialType>(ty0) && dyn_cast<SequentialType>(ty1)) {
            //Ensure that their #elem are same.
            if (dyn_cast<SequentialType>(ty0)->getNumElements() != dyn_cast<SequentialType>(ty1)->getNumElements()) {
                return false;
            }
        }
        //In the end compare the contained sub types one by one.
        for (unsigned i = 0; i < n; ++i) {
#ifdef DEBUG_TYPE_CMP
            dbgs() << i << ": " << InstructionUtils::getTypeStr(ty0->getContainedType(i)) << " | " 
            << InstructionUtils::getTypeStr(ty1->getContainedType(i)) << "\n";
#endif
            if (!InstructionUtils::same_types(ty0->getContainedType(i),ty1->getContainedType(i))) {
                return false;
            }
        }
        return true;
    }

    std::map<ConstantAggregate*,std::set<long>> *InstructionUtils::getUsesInStruct(Value *v) {
        static std::map<Value*,std::map<ConstantAggregate*,std::set<long>>> use_cache;
        if (!v) {
            return nullptr;
        }
        if (use_cache.find(v) != use_cache.end()) {
            return &use_cache[v];
        }
        for (Value::user_iterator i = v->user_begin(), e = v->user_end(); i != e; ++i) {
            if (dyn_cast<Instruction>(*i)) {
                //If the user is an instruction, it'll be impossible to occur in a constant struct.
                continue;
            }
            std::map<ConstantAggregate*,std::set<long>> *res = nullptr;
            std::map<ConstantAggregate*,std::set<long>> buf;
            ConstantAggregate *currConstA = dyn_cast<ConstantAggregate>(*i);
            if (currConstA) {
                //Figure out the #field
                for (unsigned c = 0; c < currConstA->getNumOperands(); ++c) {
                    Constant *constF = currConstA->getAggregateElement(c);
                    if (dyn_cast<Value>(constF) == v) {
                        buf[currConstA].insert((long)c);
                    }
                }
                res = &buf;
            }else {
                res = InstructionUtils::getUsesInStruct(*i);
            }
            if (!res || res->empty()) {
                continue;
            }
            //merge
            for (auto& x : *res) {
                if (use_cache[v].find(x.first) == use_cache[v].end()) {
                    use_cache[v][x.first] = x.second;
                }else {
                    use_cache[v][x.first].insert(x.second.begin(),x.second.end());
                }
            }
        }
        if (use_cache.find(v) != use_cache.end()) {
            return &use_cache[v];
        }
        return nullptr;
    }

    //Create a new GEP with up to ith operand of the original GEP.
    GetElementPtrInst *InstructionUtils::createSubGEP(GEPOperator* gep,unsigned i) {
        if (!gep || i < 1) {
            return nullptr;
        }
        if (i >= gep->getNumOperands()) {
            i = gep->getNumOperands() - 1;
        }
        std::vector<Value*> indices;
        for (int t=1; t<=i; ++t) {
            indices.push_back(gep->getOperand(t));
        }
        ArrayRef<Value*> IdxList(indices);
        return GetElementPtrInst::Create(nullptr/*PointeeType*/, gep->getPointerOperand()/*Value *Ptr*/, IdxList/*ArrayRef<Value*> IdxList*//*const Twine &NameStr="", Instruction *InsertBefore=nullptr*/);
    }

    //To decide whether a Instruction is generated and inserted by ASAN.
    //NOTE: I simply use a pattern I found from the ASAN instrumented code here, may need to be updated later.  
    //Pattern 0, E.g.:
    /***********************************************************************
    73:                                               ; preds = %63, %72
    %74 = load i64, i64* %65, align 8, !dbg !13242
    call void @llvm.dbg.value(metadata i64* %65, metadata !12875, metadata !DIExpression(DW_OP_deref)) #9, !dbg !13241
    %bp.i = getelementptr inbounds %struct.pt_regs, %struct.pt_regs* %53, i64 0, i32 4, !dbg !13243
    %75 = ptrtoint i64* %bp.i to i64, !dbg !13244
    %76 = lshr i64 %75, 3, !dbg !13244
    %77 = add i64 %76, -2305847407260205056, !dbg !13244
    %78 = inttoptr i64 %77 to i8*, !dbg !13244
    %79 = load i8, i8* %78, !dbg !13244
    %80 = icmp ne i8 %79, 0, !dbg !13244
    br i1 %80, label %81, label %82, !dbg !13244

    81:                                               ; preds = %73
    call void @__asan_report_store8_noabort(i64 %75), !dbg !13244
    call void asm sideeffect "", ""(), !dbg !13244
    br label %82, !dbg !13244
    ************************************************************************/
    //the arg "%75" of "__asan_report_store8_noabort()" -- the call instruction itself all belong to ASAN instructions
    //Pattern 1, E.g.:
    /***********************************************************************
    158:                                              ; preds = %142, %157
    store i32 %143, i32* %144, align 4, !dbg !13257
    %debug_id19 = getelementptr inbounds %struct.binder_ref_data, %struct.binder_ref_data* %src_ref, i64 0, i32 0, !dbg !13258
    %159 = ptrtoint i32* %debug_id19 to i64, !dbg !13258
    %160 = lshr i64 %159, 3, !dbg !13258
    %161 = add i64 %160, -2305847407260205056, !dbg !13258
    %162 = inttoptr i64 %161 to i8*, !dbg !13258
    %163 = load i8, i8* %162, !dbg !13258
    %164 = icmp ne i8 %163, 0, !dbg !13258
    br i1 %164, label %165, label %172, !dbg !13258, !prof !12767

    165:                                              ; preds = %158
    %166 = and i64 %159, 7, !dbg !13258
    %167 = add i64 %166, 3, !dbg !13258
    %168 = trunc i64 %167 to i8, !dbg !13258
    %169 = icmp sge i8 %168, %163, !dbg !13258
    br i1 %169, label %170, label %171, !dbg !13258

    170:                                              ; preds = %165
    call void @__asan_report_load4_noabort(i64 %159), !dbg !13258
    call void asm sideeffect "", ""(), !dbg !13258
    br label %171, !dbg !13258
    ************************************************************************/
    //The difference is from %159 to the call inst there are three BBs instead of 2 in the pattern 0.
    bool InstructionUtils::isAsanInst(Instruction *inst) {
        //Set up a cache.
        static std::map<Function*,std::set<Instruction*>> asanInstCache;
        if (!inst) {
            return false;
        }
        Function *func = inst->getFunction();
        if (!func) {
            return false;
        }
        //We will generate the results for all instructions in the host function per invocation,
        //so if current inst's host function is already in the cache, we already have the results for current inst.
        if (asanInstCache.find(func) != asanInstCache.end()) {
            bool r = (asanInstCache[func].find(inst) != asanInstCache[func].end());
#ifdef DEBUG_IS_ASAN_INST
            if (r) {
                dbgs() << "InstructionUtils::isAsanInst(): " << InstructionUtils::getValueStr(inst) << " is an asan inst!\n";
            }
#endif
            return r;
        }
        //Ok, now analyze the host function to identify all ASAN related insts according to the patterns.
        asanInstCache[func].clear();
        for (BasicBlock &bb : *func) {
            //Step 0: get all BBs that invoke __asan_report_XXX.
            Instruction *repInst = InstructionUtils::isAsanReportBB(&bb);
            if (repInst == nullptr) {
                continue;
            }
            //Step 1: add all insts in the middle (between the report inst and the call inst) to the cache.
            BasicBlock *m_bb = bb.getSinglePredecessor();
            BasicBlock *c_bb = repInst->getParent();
            if (!m_bb || !c_bb) {
                continue;
            }
            if (m_bb == c_bb) {
                //Pattern 0.
                m_bb = nullptr;
            }else if (m_bb->getSinglePredecessor() != c_bb) {
                //Cannot match any patterns.
                continue;
            }
            std::set<Instruction*> asanInsts;
            asanInsts.clear();
            //If the intermiediate BB is valid, we should add all its insts to the asan-related insts.
            bool is_asan_bb = true;
            if (m_bb) {
                for (Instruction &i : *m_bb) {
                    if (!InstructionUtils::isPotentialAsanInst(&i)) {
                        is_asan_bb = false;
                        break;
                    }
                    asanInsts.insert(&i);
                }
                if (!is_asan_bb) {
                    continue;
                }
            }
            bool after_rep_inst = false;
            is_asan_bb = true;
            for (Instruction &i : *c_bb) {
                if (&i == repInst) {
                    after_rep_inst = true;
                }
                if (!after_rep_inst) {
                    continue;
                }
                if (!InstructionUtils::isPotentialAsanInst(&i)) {
                    is_asan_bb = false;
                    break;
                }
                asanInsts.insert(&i);
            }
            if (!is_asan_bb) {
                continue;
            }
            asanInstCache[func].insert(asanInsts.begin(),asanInsts.end());
        }
        bool r = (asanInstCache[func].find(inst) != asanInstCache[func].end());
#ifdef DEBUG_IS_ASAN_INST
        if (r) {
            dbgs() << "InstructionUtils::isAsanInst(): " << InstructionUtils::getValueStr(inst) << " is an asan inst!\n";
        }
#endif
        return r;
    }

    //An ASAN error report BB is as below:
    /*****************************************
    170:                                              ; preds = %165
    call void @__asan_report_load4_noabort(i64 %159), !dbg !13258
    call void asm sideeffect "", ""(), !dbg !13258
    br label %171, !dbg !13258
    *****************************************/
    //If it's an ASAN report BB, return the variable/inst in the report (i.e. the report function's arg: %159 in above example).
    Instruction *InstructionUtils::isAsanReportBB(BasicBlock *bb) {
        if (!bb) {
            return nullptr;
        }
        //The Asan report BB only has one predecessor.
        if (bb->getSinglePredecessor() == nullptr) {
            return nullptr;
        }
        Instruction *firstInst = &(*(bb->begin()));
        if (!firstInst || !dyn_cast<CallInst>(firstInst)) {
            return nullptr;
        }
        CallInst *repInst = dyn_cast<CallInst>(firstInst);
        std::string funcname = InstructionUtils::getCalleeName(repInst,false);
        if (funcname.find("__asan_report_") == 0) {
            //Return the inst/value as the arg.
            Value *arg = repInst->getArgOperand(0);
            return (arg ? dyn_cast<Instruction>(arg) : nullptr);
        }
        return nullptr;
    }

    bool InstructionUtils::isPotentialAsanInst(Instruction *inst) {
        if (!inst) {
            return false;
        }
        //Asan inserted insts don't have names.
        if (inst->hasName()) {
            return false;
        }
        //As far as I can see now, Asan will not insert any "store".
        if (dyn_cast<StoreInst>(inst)) {
            return false;
        }
        return true;
    }

    //Given a type, return the field ty desc for its offset 0.
    FieldDesc *InstructionUtils::getHeadFieldDesc(Type *ty) {
        static std::map<Type*,FieldDesc*> hdescs;
        if (!ty) {
            return nullptr;
        }
        if (hdescs.find(ty) != hdescs.end()) {
            return hdescs[ty];
        }
        FieldDesc *fd = new FieldDesc();
        fd->bitoff = 0;
        Type *ety = ty;
        while (ety) {
            fd->tys.push_back(ety);
            if (dyn_cast<CompositeType>(ety)) {
                //We need to reserve the innermost to outermost host order.
                fd->host_tys.insert(fd->host_tys.begin(),ety);
                fd->fid.push_back(0);
                ety = dyn_cast<CompositeType>(ety)->getTypeAtIndex((unsigned)0);
            }else {
                break;
            }
        }
        hdescs[ty] = fd;
        return fd;
    }

    //We want to analyze a struct type, figuring out all possible fields types at each available offset in bits,
    //this includes the internal fields in (nested) embedded structs which is not supported by original llvm API.
    std::vector<FieldDesc*> *InstructionUtils::getCompTyDesc(DataLayout *dl, CompositeType *ty) {
        static std::map<CompositeType*,std::vector<FieldDesc*>> descs;
#ifdef DEBUG_GET_TY_DESC
        dbgs() << "getCompTyDesc(): type: " << InstructionUtils::getTypeStr(ty) << "\n";
#endif
        if (!ty) {
            return nullptr;
        }
        if (descs.find(ty) != descs.end()) {
#ifdef DEBUG_GET_TY_DESC
            dbgs() << "getCompTyDesc(): The type desc is in the cache!\n";
#endif
            return &descs[ty];
        }
        std::vector<FieldDesc*> resDesc;
        if (dyn_cast<SequentialType>(ty)) {
            SequentialType *seqTy = dyn_cast<SequentialType>(ty);
            //NOTE: in the kernel we can often see the zero-length array at the end of a struct (i.e. flexible length array).
            //This is normal so we shouldn't return nullptr, instead we return a null content resDesc in the end of this function.
            if (seqTy->getNumElements() > 0) {
                Type *aty = seqTy->getElementType();
                if (!aty) {
                    return nullptr;
                }
                std::vector<FieldDesc*> edesc, *pdesc = nullptr;
                if (dyn_cast<CompositeType>(aty)) {
                    pdesc = InstructionUtils::getCompTyDesc(dl,dyn_cast<CompositeType>(aty));
                }
                if (!pdesc) {
                    //Either non-composite element or failed to get type desc of the composite element, just treat the element as an atom.
                    FieldDesc *fd = new FieldDesc();
                    fd->tys.push_back(aty);
                    fd->bitoff = 0;
                    edesc.push_back(fd);
                    pdesc = &edesc;
                }
                //NOTE: we use alloc size here since aty will be consecutively stored in the array, so we consider its alloc size.
                unsigned step = dl->getTypeAllocSizeInBits(aty);
                for (unsigned i = 0; i < seqTy->getNumElements(); ++i) {
                    for (unsigned j = 0; j < pdesc->size(); ++j) {
                        FieldDesc *fd = new FieldDesc((*pdesc)[j]);
                        if (!i && !j) {
                            fd->tys.push_back(seqTy);
                        }
                        fd->host_tys.push_back(seqTy);
                        fd->fid.push_back(i);
                        fd->bitoff += (step*i);
                        resDesc.push_back(fd);
                    }
                }
            }
        }else if (dyn_cast<StructType>(ty)) {
            StructType *stTy = dyn_cast<StructType>(ty);
            if (stTy->isOpaque() || !dl) {
                return nullptr;
            }
            const StructLayout *stLayout = dl->getStructLayout(stTy);
            if (!stLayout) {
                return nullptr;
            }
            for (unsigned i = 0; i < stTy->getNumElements(); ++i) {
                Type *ety = stTy->getElementType(i);
                if (!ety) {
                    continue;
                }
                unsigned boff = stLayout->getElementOffsetInBits(i); 
                if (dyn_cast<CompositeType>(ety)) {
                    //Ok the element is an embedded composite type.
                    std::vector<FieldDesc*> *pdesc = InstructionUtils::getCompTyDesc(dl,dyn_cast<CompositeType>(ety));
                    if (pdesc) {
                        for (unsigned j = 0; j < pdesc->size(); ++j) {
                            FieldDesc *fd = new FieldDesc((*pdesc)[j]);
                            if (!i && !j) {
                                fd->tys.push_back(stTy);
                            }
                            fd->host_tys.push_back(stTy);
                            fd->fid.push_back(i);
                            fd->bitoff += boff;
                            resDesc.push_back(fd);
                        }
                        continue;
                    }
                }
                //Ok, we either have a non-composite field, or we failed to get the detailed type desc of the composite field,
                //we will just treat the field as an atom.
                FieldDesc *fd = new FieldDesc();
                if (!i) {
                    fd->tys.push_back(stTy);
                }
                fd->tys.push_back(ety);
                fd->host_tys.push_back(stTy);
                fd->fid.push_back(i);
                fd->bitoff = boff;
                resDesc.push_back(fd);
            }
        }else {
            dbgs() << "Cannot recognize the CompositeType: " << InstructionUtils::getTypeStr(ty) << "\n";
            assert(false);
        }
#ifdef DEBUG_GET_TY_DESC
        dbgs() << ">> The type desc for: " << InstructionUtils::getTypeStr(ty) << "\n";
        for (FieldDesc *fd : resDesc) {
            fd->print(dbgs());
        }
#endif
        descs[ty] = resDesc;
        return &descs[ty];
    }

    int InstructionUtils::locateFieldInTyDesc(std::vector<FieldDesc*> *tydesc, unsigned fid) {
        if (!tydesc || tydesc->size() == 0) {
            return -1;
        }
        for (int i = 0; i < tydesc->size(); ++i) {
            FieldDesc *fd = (*tydesc)[i];
            if (fd) {
                //There may exist some embedded composite typed fields in the host obj, but the "fid" here refers only to the index within the outmost host obj.
                unsigned curid = fd->fid[fd->fid.size()-1];
                if (curid == fid) {
                    return i;
                }else if (curid > fid) {
                    //The field id in the vector is in the ascending order.
                    //NOTE: it should be impossible to reach here if the "tydesc" is correct...
                    return -1;
                }
            }
        }
        return -1;
    }

    int InstructionUtils::locateBitsoffInTyDesc(std::vector<FieldDesc*> *tydesc, int boff) {
        if (!tydesc || tydesc->size() == 0) {
            return -1;
        }
        for (int i = 0; i < tydesc->size(); ++i) {
            FieldDesc *fd = (*tydesc)[i];
            if (fd) {
                if (fd->bitoff == boff) {
                    return i;
                }else if (fd->bitoff > boff) {
                    return -1;
                }
            }
        }
        return -1;
    }

    bool InstructionUtils::ptr_sub_type(Type *ty0, Type *ty1) {
        if (!ty0 || !ty1) {
            return false;
        }
        if (!ty1->isPointerTy()) {
            return InstructionUtils::same_types(ty0,ty1);
        }
        while (ty1->isPointerTy()) {
            ty1 = ty1->getPointerElementType();
            if (InstructionUtils::same_types(ty0,ty1)) {
                return true;
            }
        }
        return false;
    }

    bool InstructionUtils::isTyUsedByFunc(Type *ty, Function *func) {
        if (!ty || !func) {
            return false;
        }
        for (Value& v : func->args()) {
            if (InstructionUtils::ptr_sub_type(ty,v.getType())) {
                return true;
            }
        }
        for (BasicBlock& bb : *func) {
            for (Instruction& ins : bb) {
                if (InstructionUtils::ptr_sub_type(ty,ins.getType())) {
                    return true;
                }
                for (unsigned i = 0; i < ins.getNumOperands(); ++i) {
                    Value *v = ins.getOperand(i);
                    if (InstructionUtils::ptr_sub_type(ty,v->getType())) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    void FieldDesc::print(raw_ostream &OS) {
        OS << "+" << this->bitoff << ": ";
        for (Type *ty : this->tys) {
            OS << InstructionUtils::getTypeStr(ty) << " ||| ";
        }
        OS << "\nhost: ";
        if (this->host_tys.size() > 0 && this->host_tys.size() == this->fid.size()) {
            for (int i = this->fid.size()-1; i >= 0; --i) {
                OS << InstructionUtils::getTypeStr(this->host_tys[i]) << " | " << this->fid[i] << " --> ";
            }
        }else {
            OS << "#host_tys: " << this->host_tys.size() << " #fid: " << this->fid.size();
        }
        OS << "\n";
    }

    void FieldDesc::print_path(raw_ostream &OS) {
        if (this->host_tys.size() > 0 && this->host_tys.size() == this->fid.size()) {
            for (int i = this->fid.size()-1; i >= 0; --i) {
                OS << InstructionUtils::getTypeStr(this->host_tys[i]) << " | " << this->fid[i] << " --> ";
            }
        }else {
            OS << "Error! #host_tys: " << this->host_tys.size() << " #fid: " << this->fid.size();
        }
        OS << "\n";
    }

    int FieldDesc::findTy(Type *ty, bool wildp) {
        if (ty) {
            for (int i = 0; i < this->tys.size(); ++i) {
                if (InstructionUtils::same_types(this->tys[i],ty,wildp)) {
                    return i;
                }
            }
        }
        return -1;
    }

    int FieldDesc::findHostTy(Type *ty) {
        if (ty) {
            for (int i = 0; i < this->host_tys.size(); ++i) {
                if (InstructionUtils::same_types(this->host_tys[i],ty)) {
                    return i;
                }
            }
        }
        return -1;
    }

    Type *FieldDesc::getOutermostTy() {
        if (this->host_tys.size() > 0) {
            return this->host_tys[this->host_tys.size()-1];
        }
        return nullptr;
    }

    bool InstructionUtils::isIndexValid(Type *ty, unsigned fid) {
        if (!ty) {
            return false;
        }
        if (ty->isStructTy()) {
            return (fid >= 0 && fid < ty->getStructNumElements());
        }else if (ty->isArrayTy()) {
            return (fid >= 0 && fid < ty->getArrayNumElements());
        }else if (ty->isVectorTy()) {
            //The vector can be extended at desire.
            return (fid >= 0);
        }
        //We have already covered all composite types. 
        return (fid == 0);
    }

    //////////////////////////////////////////////////////////////////////////////////////////////////////////
    //Most of below metadata related code is copied from the llvm 7.0's internal implementation on ".ll" generation.
    //https://github.com/llvm/llvm-project/blob/release/7.x/llvm/lib/IR/AsmWriter.cpp
    //I do think they should make a convenient API to enumerate all metadata nodes...
    
    //This holds all metadata nodes in the module.
    DenseMap<MDNode*, unsigned> InstructionUtils::mdnCache;

    //This holds the name->DIC mapping, the name is the struct name like "file" (no struct. prefix and no numeric suffix).
    std::map<std::string,DICompositeType*> InstructionUtils::dicMap;

    void createMetadataSlot(MDNode *N, DenseMap<MDNode*, unsigned> *mdnMap) {
        static int mdnNext = 0;
        static std::set<MDNode*> visited;
        if (!mdnMap || !N) {
            return;
        }
        if (visited.find(N) != visited.end()) {
            //Already visited.
            return;
        }
        visited.insert(N);
        //NOTE: in theory we can get *all* MDNodes, but for now we're only interested in the DICompositeType.
        if (isa<DICompositeType>(N) && mdnMap->find(N) == mdnMap->end()) {
            //the map also stores the number of each metadata node. It is the same order as in the dumped bc file.
            (*mdnMap)[N] = mdnNext++;
        }
        for (unsigned i = 0, e = N->getNumOperands(); i != e; ++i) {
            if (MDNode *Op = dyn_cast_or_null<MDNode>(N->getOperand(i))) {
                createMetadataSlot(Op,mdnMap);
            }
        }
    }

	void processGlobalObjectMetadata(const GlobalObject &GO, DenseMap<MDNode*, unsigned> *mdnMap) {
  		SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
  		GO.getAllMetadata(MDs);
  		for (auto &MD : MDs)
    		createMetadataSlot(MD.second,mdnMap);
	}

	void processInstructionMetadata(const Instruction &I, DenseMap<MDNode*, unsigned> *mdnMap) {
  		// Process metadata used directly by intrinsics.
  		if (const CallInst *CI = dyn_cast<CallInst>(&I))
    		if (Function *F = CI->getCalledFunction())
      			if (F->isIntrinsic())
        			for (auto &Op : I.operands())
          				if (auto *V = dyn_cast_or_null<MetadataAsValue>(Op))
            				if (MDNode *N = dyn_cast<MDNode>(V->getMetadata()))
              					createMetadataSlot(N,mdnMap);
  		// Process metadata attached to this instruction.
  		SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
  		I.getAllMetadata(MDs);
  		for (auto &MD : MDs)
    		createMetadataSlot(MD.second,mdnMap);
	}

    int InstructionUtils::getAllMDNodes(Module *mod) {
        if (!InstructionUtils::mdnCache.empty()) {
            //Already inited
            return 0;
        }
        if (!mod) {
            return 1;
        }
        //Get all metadata nodes for global variables.
        for (const GlobalVariable &Var : mod->globals()) {
            processGlobalObjectMetadata(Var,&InstructionUtils::mdnCache);
        }
        //Add metadata used by named metadata.
  		for (const NamedMDNode &NMD : mod->named_metadata()) {
    		for (unsigned i = 0, e = NMD.getNumOperands(); i != e; ++i)
      			createMetadataSlot(NMD.getOperand(i),&InstructionUtils::mdnCache);
  		}
        //Add metadata used by all functions and instructions.
		for (const Function &F : *mod) {
            processGlobalObjectMetadata(F,&InstructionUtils::mdnCache);
            for (auto &BB : F) {
                for (auto &I : BB)
                    processInstructionMetadata(I,&InstructionUtils::mdnCache);
            }
        }
        return 0;
    }

    int InstructionUtils::setupDicMap(Module *mod) {
        if (!InstructionUtils::dicMap.empty()) {
            //Already inited.
            return 0;
        }
        if (InstructionUtils::mdnCache.empty()) {
            if (!mod) {
                return 1;
            }
            InstructionUtils::getAllMDNodes(mod);
        }
        //Convert mdnCache to dicMap.
        for (auto& e : InstructionUtils::mdnCache) {
            DICompositeType *nd = dyn_cast<DICompositeType>(e.first);
            if (nd && !nd->getName().empty()) {
                InstructionUtils::dicMap[nd->getName().str()] = nd;
            }
        }
        return 1;
    }

    //////////////////////////////////////////////////////////////////////////////////////////////////////////
 
    //Get the name of a specified field within a struct type, w/ the debug info.
    std::string InstructionUtils::getStFieldName(Module *mod, StructType *ty, unsigned fid) {
        //struct type --> field id --> field name
        static std::map<std::string,std::map<unsigned,std::string>> ncache;
#ifdef DEBUG_RELATE_TYPE_NAME
        dbgs() << "InstructionUtils::getStFieldName(): for ty: " << InstructionUtils::getTypeStr(ty) << " | " << fid << "\n";
#endif
        if (!mod || !ty || !ty->hasName()) {
            return "";
        }
        //Get the struct name.
        std::string stn = ty->getName().str();
        stn = InstructionUtils::trim_struct_name(stn);
#ifdef DEBUG_RELATE_TYPE_NAME
        dbgs() << "InstructionUtils::getStFieldName(): type name: " << stn << "\n";
#endif
        if (stn == "anon") {
            //We have no field names for anonymized struct. 
            return "";
        }
        if (ncache.find(stn) == ncache.end()) {
            if (InstructionUtils::dicMap.empty()) {
                InstructionUtils::setupDicMap(mod);
            }
            if (InstructionUtils::dicMap.find(stn) == InstructionUtils::dicMap.end()) {
#ifdef DEBUG_RELATE_TYPE_NAME
                dbgs() << "InstructionUtils::getStFieldName(): cannot get the DICompositeType MDNode!\n";
#endif
                return "";
            }
            DICompositeType *nmd = InstructionUtils::dicMap[stn];
            //Ok, got it.
#ifdef DEBUG_RELATE_TYPE_NAME
            dbgs() << "InstructionUtils::getStFieldName(): Got the DICompositeType MDNode!\n";
#endif
            DINodeArray dia=nmd->getElements(); 
            for (unsigned j = 0; j < dia.size(); ++j) {
                DIType *field=dyn_cast<DIType>(dia[j]);
                if (!field) {
#ifdef DEBUG_RELATE_TYPE_NAME
                    dbgs() << "InstructionUtils::getStFieldName(): cannot get the DIType for field: " << j << "\n";
#endif
                    continue;
                }
                ncache[stn][j] = field->getName().str();
            }
        }//if not in cache.
        //Note that as long as we processed one request for a single field in a certain StructType, we will cache all fields in the same type.
        if (ncache.find(stn) != ncache.end()) {
            if (ncache[stn].find(fid) != ncache[stn].end()) {
#ifdef DEBUG_RELATE_TYPE_NAME
                dbgs() << "InstructionUtils::getStFieldName(): Got the result from the cache: " << ncache[stn][fid] << "\n";
#endif
                return ncache[stn][fid];
            }else {
#ifdef DEBUG_RELATE_TYPE_NAME
                dbgs() << "InstructionUtils::getStFieldName(): Got the type from the cache but not the field!\n";
#endif
                return "";
            }
        }
        return "";
    }

    void InstructionUtils::printCallingCtx(raw_ostream &O, std::vector<Instruction*> *ctx, bool lbreak) {
        if (ctx && ctx->size() > 0) {
            std::string lastFunc;
            for (Instruction *inst : *ctx) {
                if (inst && inst->getParent() && inst->getFunction()) {
                    std::string func = inst->getFunction()->getName().str();
                    if (func != lastFunc) {
                        O << func << " -> ";
                        lastFunc = func;
                    }
                }
            }
        }
        if (lbreak) {
            O << "\n";
        }
    }

    //If "bit" is zero, integer w/ any width will do.
    bool InstructionUtils::isPrimitiveTy(Type *ty, int bit) {
        if (ty) {
            return (ty->isVoidTy() || (bit > 0 ? ty->isIntegerTy(bit) : ty->isIntegerTy()));
        }
        return true;
    }

    bool InstructionUtils::isNullCompTy(Type *ty) {
        if (ty && dyn_cast<CompositeType>(ty)) {
            return (InstructionUtils::isOpaqueSt(ty) || !InstructionUtils::isIndexValid(ty,0));
        }
        return false;
    }

    bool InstructionUtils::isNullCompPtr(Type *ty)  {
        if (!ty || !ty->isPointerTy()) {
            return false;
        }
        return InstructionUtils::isNullCompTy(ty->getPointerElementType());
    }

    bool InstructionUtils::isPrimitivePtr(Type *ty, int bit) {
        if (!ty || !ty->isPointerTy()) {
            return false;
        }
        return InstructionUtils::isPrimitiveTy(ty->getPointerElementType(),bit);
    }

    //Note: the struct name is like "file"
    Type *InstructionUtils::getStTypeByName(Module *mod, std::string &n) {
        static std::map<std::string,StructType*> tyMap;
        static std::map<std::string,std::set<StructType*>> tysMap;
#ifdef DEBUG_RELATE_TYPE_NAME
        dbgs() << "InstructionUtils::getStTypeByName(): name: " << n << "\n";
#endif
        if (tyMap.empty()) {
#ifdef DEBUG_RELATE_TYPE_NAME
            dbgs() << "InstructionUtils::getStTypeByName(): set up the tyMap...\n";
#endif
            //Setup the cache for all available struct types.
            if (!mod) {
                return nullptr;
            }
            std::vector<StructType*> tys = mod->getIdentifiedStructTypes();
            for (StructType *ty : tys) {
                if (ty && ty->hasName()) {
                    std::string s = ty->getName().str();
                    //Strip the name prefix
                    if (s.find("struct.") == 0) {
                        s = s.substr(7);
                    }
                    if (s.find("anon") == 0) {
                        //If it's an anonymized struct, different numeric suffixes mean different structures, so we need to preserve the suffix.
                        tysMap[s].insert(ty);
                        continue;
                    }
                    //Strip the numeric suffix.
                    InstructionUtils::trim_num_suffix(&s);
                    tysMap[s].insert(ty);
                }
            }
            //Now try to consolidate the tysMap to tyMap.
            for (auto &e : tysMap) {
                std::set<StructType*> &ts = e.second;
                if (ts.size() == 0) {
                    continue;
                }
                if (ts.size() == 1) {
                    tyMap[e.first] = *(ts.begin());
                    continue;
                }
                //Pick the type w/ the shortest name (likely that's the one w/o the numeric suffix).
                StructType *pt = *(ts.begin());
                for (StructType *t : ts) {
                    if (t->getName().str().size() < pt->getName().str().size()) {
                        pt = t;
                    }
                }
                tyMap[e.first] = pt;
            }
#ifdef DEBUG_RELATE_TYPE_NAME
            dbgs() << "InstructionUtils::getStTypeByName(): done. #tyMap: " << tyMap.size() << "\n";
#endif
        }
        if (tyMap.find(n) != tyMap.end()) {
#ifdef DEBUG_RELATE_TYPE_NAME
            dbgs() << "InstructionUtils::getStTypeByName(): Got the type: " << InstructionUtils::getTypeStr(tyMap[n]) << "\n";
#endif
            return tyMap[n];
        }
        return nullptr;
    }

    bool InstructionUtils::isOpaqueSt(Type *ty) {
        return (ty && ty->isStructTy() && dyn_cast<StructType>(ty)->isOpaque());
    }

    long InstructionUtils::calcGEPTotalOffsetInBits(GEPOperator *gep, DataLayout *dl, int *rc) {
        if (rc) {
            *rc = -1;
        }
        if (!gep || !dl) {
            return 0;
        }
        //Get the original pointer operand used in this GEP and its type info.
        Value *orgPointer = gep->getPointerOperand();
        if (!orgPointer) {
            return 0;
        }
        Type *basePointerTy = orgPointer->getType();
        Type *basePointeeTy = nullptr;
        if (basePointerTy && basePointerTy->isPointerTy()) {
            basePointeeTy = basePointerTy->getPointerElementType();
        }
        if (!basePointeeTy) {
            return 0;
        }
        Type *curTy = basePointeeTy;
        long sumoff = 0;
        //Scan each index and calculate the total offset.
        int i;
        for (i = 1; i < gep->getNumOperands(); ++i) {
            ConstantInt *CI = dyn_cast<ConstantInt>(gep->getOperand(i));
            long fid = 0;
            bool is_var_fid = false;
            if (!CI) {
                //TODO: should we directly return here? We cannot get the accurate total offset anyway.
                is_var_fid = true;
            }else {
                fid = CI->getZExtValue();
            }
            if (!curTy) {
                break;
            }
            if (i > 1) {
                if (fid < 0) {
                    //TODO: Is it possible that the non-1st index is negative? Seems impossible...
                    dbgs() << "!!! InstructionUtils::calcGEPTotalOffsetInBits(): negative non-1st index: " << InstructionUtils::getValueStr(gep) << "\n";
                    break;
                }
                if (dyn_cast<CompositeType>(curTy) && InstructionUtils::isIndexValid(curTy,fid)) {
                    //Get the bit offset of curent fid in current host type.
                    std::vector<FieldDesc*> *tyd = InstructionUtils::getCompTyDesc(dl,dyn_cast<CompositeType>(curTy));
                    int ind = InstructionUtils::locateFieldInTyDesc(tyd,fid);
                    if (ind < 0) {
                        break;
                    }
                    sumoff += (long)((*tyd)[ind]->bitoff);
                    //Get the subsequent field type.
                    curTy = dyn_cast<CompositeType>(curTy)->getTypeAtIndex((unsigned)fid);
                } else {
                    break;
                }
            } else {
                //NOTE: use alloc size here since 1st index is for an array of curTy.
                long width = dl->getTypeAllocSizeInBits(curTy);
                sumoff += (width*fid);
            }
        }
        if (i >= gep->getNumOperands()) {
            *rc = 0;
        }
        return sumoff;
    }

    std::string& InstructionUtils::getTypeName(Type *ty) {
        static std::map<Type*,std::string> cache; 
        if (cache.find(ty) == cache.end()) {
            if (!ty) {
                cache[ty].clear();
            }else if (!dyn_cast<CompositeType>(ty)) {
                cache[ty] = InstructionUtils::getTypeStr(ty);
            }else if (dyn_cast<StructType>(ty)) {
                if (dyn_cast<StructType>(ty)->hasName()) {
                    cache[ty] = ty->getStructName().str();
                }else {
                    cache[ty] = InstructionUtils::getTypeStr(ty);
                }
            }else if (dyn_cast<SequentialType>(ty)) {
                std::string es = InstructionUtils::getTypeName(dyn_cast<SequentialType>(ty)->getElementType());
                cache[ty] = "[" + es + "]*" + std::to_string(dyn_cast<SequentialType>(ty)->getNumElements());
            }else {
                cache[ty] = "UNK";
            }
        }
        return cache[ty];
    }

    bool TypeField::is_same_ty(TypeField *tf) {
        if (!tf) {
            return false;
        }
        return (this->fid == tf->fid && InstructionUtils::same_types(this->ty,tf->ty));
    }

    std::chrono::time_point<std::chrono::system_clock> InstructionUtils::getCurTime(raw_ostream *OS) {
        auto t = std::chrono::system_clock::now();
        if (OS) {
            std::time_t tt = std::chrono::system_clock::to_time_t(t);
            (*OS) << std::ctime(&tt) << "\n";
        }
        return t;
    }

    std::chrono::duration<double> InstructionUtils::getTimeDuration(std::chrono::time_point<std::chrono::system_clock> prev, raw_ostream *OS) {
        auto t = std::chrono::system_clock::now();
        std::chrono::duration<double> du = t - prev;
        if (OS) {
            (*OS) << du.count() << "s\n";
        }
        return du;
    }

    int dumpFuncGraph(Function *f) {
        if (!f) {
            dbgs() << "dumpFuncGraph(): null func ptr!\n";
            return 1;
        }
        std::string Filename = "cfg_dot_files/cfg." + f->getName().str() + ".dot";
        dbgs() << "dumpFuncGraph(): Writing '" << Filename << "'...\n";
        std::error_code ErrorInfo;
        raw_fd_ostream File(Filename, ErrorInfo, sys::fs::F_Text);
        if (ErrorInfo.value() == 0)
            WriteGraph(File, f);
        else
            dbgs() << "dumpFuncGraph(): error opening file for writing!\n";
            return 1;
        dbgs() << "dumpFuncGraph(): done!\n";
        return 0;
    }

    DIType *getTyFromDbgInfo(Function *f, Value *v) {
        if (!f || !v) {
            return nullptr;
        }
        DILocalVariable *div = nullptr;
        for (BasicBlock &bb : *f) {
            for (Instruction &inst : bb) {
                if (dyn_cast<DbgDeclareInst>(&inst)) {
                    DbgDeclareInst *dinst = dyn_cast<DbgDeclareInst>(&inst);
                    if (dinst->getAddress() == v) {
                        div = dinst->getVariable();
                        goto out;
                    }
                }else if (dyn_cast<DbgValueInst>(&inst)) {
                    DbgValueInst *dinst = dyn_cast<DbgValueInst>(&inst);
                    if (dinst->getValue() == v) {
                        div = dinst->getVariable();
                        goto out;
                    }
                }
            }
        }
out:
        if (!div) {
            return nullptr;
        }
        return div->getType();
    }

    Type *getPointeeTyFromDITy(Module *mod, DIType *div) {
        if (!div) {
            return nullptr;
        }
        //Record the pointer indirection layer.
        int layer = 0;
        Type *ty = nullptr;
        while (div) {
            DIDerivedType *dity = dyn_cast<DIDerivedType>(div);
            if (dity) {
                //One more layer of type indirection, see whether it's a pointer..
                if (dity->getTag() == llvm::dwarf::DW_TAG_pointer_type || 
                    dity->getTag() == llvm::dwarf::DW_TAG_ptr_to_member_type) {
                    ++layer;
                }
                div = dity->getBaseType();
            }else {
                //We have reached the non-pointer base type, record it.
                //TODO: get the Type of non-composite types as well (see the static methods in the Type class).
                if (dyn_cast<DICompositeType>(div)) {
                    std::string stn = div->getName().str();
                    ty = InstructionUtils::getStTypeByName(mod, stn);
                }
                break;
            }
        }
        //Construct the pointee type according to the pointer indirection layer.
        if (!ty) {
            return nullptr;
        }
        for (int i = 1; i < layer; ++i) {
            ty = ty->getPointerTo();
        }
        return ty;
    }

    //Return 1 if ty0 contain ty1 (as its heading part), -1 if the opposite, 0 if they are equal, -2 if they are not compatiable.
    int testTyCompat(Type *ty0, Type *ty1) {
        if (!ty0 != !ty1) {
            return (ty0 ? 1 : -1);
        }
        if (!ty0) {
            //Both are nullptr.
            return 0;
        }
        //From now on both types cannot be null.
        if (InstructionUtils::same_types(ty0,ty1)) {
            return 0;
        }
        if (!dyn_cast<CompositeType>(ty0) && !dyn_cast<CompositeType>(ty1)) {
            //TODO: consider more special cases, like i8* can be potentially converted to other pointer types.
            if (!ty0->isVoidTy() != !ty1->isVoidTy()) {
                return (ty0->isVoidTy() ? -1 : 1);
            }
            //E.g. i32 should contain i8, etc.
            if (ty0->isIntegerTy() && ty1->isIntegerTy()) {
                int r = (int)ty0->getIntegerBitWidth() - (int)ty1->getIntegerBitWidth();
                return (r > 0 ? 1 : (r < 0 ? -1 : 0));
            }
            //i8 can match anything
            if (InstructionUtils::isPrimitiveTy(ty0,8) || InstructionUtils::isPrimitiveTy(ty1,8)) {
                //Only one of them is i8.
                return (InstructionUtils::isPrimitiveTy(ty0,8) ? -1 : 1);
            }
            return -2;
        }
        //From now on at least one of the two types is composite.
        FieldDesc *fd0 = InstructionUtils::getHeadFieldDesc(ty0);
        FieldDesc *fd1 = InstructionUtils::getHeadFieldDesc(ty1);
        if (!fd0 || !fd1) {
            return -2;
        }
        if (fd0->tys.size() == fd1->tys.size()) {
            //Both types should be composite, and one cannot contain the other, and they are not the same types.
            return -2;
        }
        if (fd0->tys.size() > fd1->tys.size()) {
            return (fd0->findTy(ty1,true) >= 0 ? 1 : -2);
        }
        return (fd1->findTy(ty0,true) >= 0 ? -1 : -2);
    }

    //If there are two potential types for a same value but they are not compatiable, we try to select one
    //or none of them, according to some domain knowledges.
    //Currently we deal w/ one situation here, e.g.
    //-------------------------------------------------------------------
    //  struct snd_timer_instance *ts;
    //  list_for_each_entry(ts, &ti->slave_active_head, active_list)
    //-------------------------------------------------------------------
    //In theory each iteration of the macro needs to construct a snd_timer_instance* (w/ container_of) and assign it to "ts",
    //but clang optimization usually directly uses the list_head* (i.e. pointer to the "active_list" field in snd_timer_instance)
    //to access other fields in the host struct w/ the relative offset. So in many cases, "ts" is a list_head* (according to cast instr),
    //but snd_timer_instance* according to the src dbg info. In this case we will choose list_head* as is, and infer the container later.
    Type *solveConflictTys(Value *v, Type *ty0, Type *ty1) {
        StructType *sty0 = dyn_cast<StructType>(ty0);
        StructType *sty1 = dyn_cast<StructType>(ty1);
        if (sty0 && sty1) {
            std::string n0 = sty0->hasName() ? sty0->getName().str() : "";
            std::string n1 = sty1->hasName() ? sty1->getName().str() : "";
            std::string nv = (v && v->hasName()) ? v->getName().str() : "";
            if (n0.find("struct.list_head") != std::string::npos || n1.find("struct.list_head") != std::string::npos) {
                if (nv.find("pn") != std::string::npos) {
                    return ((n0.find("struct.list_head") != std::string::npos) ? ty0 : ty1);
                }
            }
        }
        return nullptr;
    }

    //Infer the pointee type of the pointer "v" from the context (e.g. cast inst involving "v") and src debug info (i.e. metadata node).
    //Note that we always try to return the largest pointee type that is compatiable w/ all other identified types. 
    Type *InstructionUtils::inferPointeeTy(Value *v) {
#ifdef DEBUG_RELATE_TYPE_NAME
        dbgs() << "InstructionUtils::inferPointeeTy() for: " << InstructionUtils::getValueStr(v) << "\n";
#endif
        static std::map<Value*,Type*> vtMap;
        if (!v) {
            return nullptr;
        }
        if (vtMap.find(v) != vtMap.end()) {
#ifdef DEBUG_RELATE_TYPE_NAME
            dbgs() << "InstructionUtils::inferPointeeTy(): res type: " << InstructionUtils::getTypeStr(vtMap[v]) << "\n";
#endif
            return vtMap[v];
        }
        //Set a default value, anyway we will not execute the below code again for the same Value.
        vtMap[v] = nullptr;
        std::set<Type*> tys;
        std::set<Type*> ctx_tys;
        //First extract the type associated w/ the value itself.
        if (v->getType() && v->getType()->isPointerTy()) {
            tys.insert(v->getType()->getPointerElementType());
            ctx_tys.insert(v->getType()->getPointerElementType());
        }
        //Now let's inspect the cast/load/gep insts involving the "v" in the context.
        std::set<Function*> funcs;
        for (User *u : v->users()) {
            //Collect the enclosing functions of this value.
            if (dyn_cast<Instruction>(u) && dyn_cast<Instruction>(u)->getParent()) {
                funcs.insert(dyn_cast<Instruction>(u)->getFunction());
            }
            if (dyn_cast<GEPOperator>(u)) {
                GEPOperator *gep = dyn_cast<GEPOperator>(u);
                //Make sure it's a GEP w/ "v" as the base pointer.
                if (gep->getPointerOperand() != v) {
                    continue;
                }
                //Get the GEP base pointer type.
                Type *ty = gep->getPointerOperandType();
                if (ty && ty->isPointerTy()) {
                    tys.insert(ty->getPointerElementType());
                    ctx_tys.insert(ty->getPointerElementType());
                }
            }else if (dyn_cast<Instruction>(u)) {
                Type *ty = nullptr;
                if (dyn_cast<CastInst>(u)) {
                    ty = dyn_cast<CastInst>(u)->getDestTy();
                }else if (dyn_cast<LoadInst>(u)) {
                    ty = dyn_cast<LoadInst>(u)->getPointerOperandType();
                }
                if (ty && ty->isPointerTy()) {
                    tys.insert(ty->getPointerElementType());
                    ctx_tys.insert(ty->getPointerElementType());
                }
            }
        }
        //Now try to get type info from the src level dbg info (i.e. metadata node).
        for (Function *f : funcs) {
            if (f) {
                //Get the src level type descriptor of "v", if any.
                DIType *dty = getTyFromDbgInfo(f,v);
                //Extract the pointee type, if it's indeed a pointer.
                Type *ty = getPointeeTyFromDITy(f->getParent(),dty);
                if (ty) {
                    tys.insert(ty);
                }
            }
        }
#ifdef DEBUG_RELATE_TYPE_NAME
        dbgs() << "InstructionUtils::inferPointeeTy(): candidate types: ";
        for (Type *ty : tys) {
            dbgs() << InstructionUtils::getTypeStr(ty) << " | ";
        }
        dbgs() << "\n";
#endif
        //Ok, now we have a set of the potential pointee types in "tys", we then need a compatiability test of these types
        //and return the largest one.
        Type *hostTy = nullptr;
        for (Type *ty : tys) {
            if (!ty) {
                continue;
            }
            if (!hostTy) {
                hostTy = ty;
                continue;
            }
            //See whether current hostTy can contain this "ty", if so, continue, otherwise, if it's conatined by "ty", update
            //current hostTy to "ty". If they are not compatiable, that means we cannot decide the correct pointee type...
            int r = testTyCompat(hostTy,ty);
#ifdef DEBUG_RELATE_TYPE_NAME
            dbgs() << "InstructionUtils::inferPointeeTy(): type compat: " << InstructionUtils::getTypeStr(hostTy) << 
            " | " << InstructionUtils::getTypeStr(ty) << " -> " << r << "\n";
#endif
            if (r == -2) {
                //The two types are not incompatiable, try to resolve the conflicts.
                Type *sty = solveConflictTys(v,hostTy,ty);
                if (!sty) {
                    //Cannot resolve the conflicts, we will just pick the type inferred from the context IR since that's how it's used.
                    if ((ctx_tys.find(hostTy) == ctx_tys.end()) != (ctx_tys.find(ty) == ctx_tys.end())) {
                        sty = (ctx_tys.find(ty) != ctx_tys.end()) ? ty : hostTy;
                    }else {
                        //Conflict types from the same source...
                        return nullptr;
                    }
                }
                hostTy = sty;
            }
            if (r == -1) {
                hostTy = ty;
            }
        }
#ifdef DEBUG_RELATE_TYPE_NAME
        dbgs() << "InstructionUtils::inferPointeeTy(): res type: " << InstructionUtils::getTypeStr(hostTy) << "\n";
#endif
        vtMap[v] = hostTy;
        return hostTy;
    }
}
