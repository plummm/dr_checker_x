#ifndef _H_RESTYPE
#define _H_RESTYPE

//Here some types used for static analysis result data exchange.
//They are defined like some SQL DB tables, some primary keys (e.g. taint tag id) are shared acorss tables.

//names for: inst, bb, func, and module
typedef std::vector<std::string> LOC_INF;

//arg no. of the func -> value set that enables to reach the mod inst
typedef std::map<unsigned, std::set<uint64_t>> ARG_CONSTRAINTS;

//mod inst ctx id -> ARG_CONSTRAINTS
typedef std::map<unsigned long,ARG_CONSTRAINTS> MOD_INF;

//module name -> func name -> BB names (whose last 'br' is affected by global states) -> br's ctx_id -> set<tag_id> that taints this br
typedef std::map<std::string,std::map<std::string,std::map<std::string,std::map<unsigned long,std::set<unsigned long>>>>> TAINTED_BR_TY;

//Analysis context map, id -> callstack
typedef std::map<unsigned long,std::vector<LOC_INF>> ANALYSIS_CTX_MAP_TY;

//The map from taint tags to their mod insts.
//tag id -> mod -> func -> BB -> inst -> MOD_INF of this mod inst
typedef std::map<unsigned long,std::map<std::string,std::map<std::string,std::map<std::string,std::map<std::string,MOD_INF>>>>> TAG_MOD_MAP_TY;

//tag id -> info (currently the type) of this tag
typedef std::map<unsigned long,std::string> TAG_INFO_TY;

//id -> the ctx of the mod inst
typedef std::map<unsigned long,std::vector<LOC_INF>> MOD_INST_CTX_MAP_TY;

#endif
