#!/usr/bin/python

#Extract and process the warnings in the log output.

import sys,os
import json

warns = []
jwarns = []

def ext_warns(log):
    global warns
    is_warn = False
    with open(log,'r') as f:
        for l in f:
            if l.startswith('@@@@@@'):
                is_warn = (not is_warn)
            elif is_warn:
                #One line per warning.
                l = l.strip()
                if l.startswith('\"warn_data\":'):
                    warns.append(l)
                    j = json.loads(l[12:])
                    jwarns.append(j)
    #TODO: Do some filtering, grouping, etc according to the warning json content.

def dump_warns_raw():
    global warns
    #Dump the warning
    for l in warns:
        print l

PATH_PREFIX = 'private/msm-google/'
URL_PREFIX = 'https://android.googlesource.com/kernel/msm/+/refs/tags/android-10.0.0_r0.56/'

def mkurl(j):
    fp = j.get('at_file','')
    ln = j.get('at_line',0)
    if fp.startswith(PATH_PREFIX):
        fp = fp[len(PATH_PREFIX):]
    return URL_PREFIX + fp + '#' + str(ln)

def get_ctx_strs(ctx):
    if (not ctx) or len(ctx) == 0:
        return []
    chain = []
    chain_comp = []
    is_entry = True
    for inst in ctx:
        func = inst.get('at_func','UNK_FUNC')
        furl = mkurl(inst)
        if is_entry:
            chain.append(func)
            s = func + ' (' + furl + ')'
            chain_comp.append(s)
        else:
            #Record the callsite info.
            ins = inst.get('instr','UNK_INST')
            s = '----> (' + furl + ' : ' + ins + ')'
            chain_comp.append(s)
        is_entry = (not is_entry)
    chain_comp.append(' -> '.join(chain))
    return chain_comp

def pprint_trace(tr):
    cur_ctx = None
    for ins in tr:
        #First we need to output the context of this inst - if we haven't done so already.
        ctx = get_ctx_strs(ins.get('ctx',[]))
        if (not cur_ctx) or cur_ctx <> ctx:
            print '#####CTX##### ' + ctx[-1]
            for i in range(len(ctx)-1):
                print ctx[i]
            print '#####INSTS#####'
            cur_ctx = ctx
        #Now print current inst.
        furl = mkurl(ins)
        inst = ins.get('instr','UNK_INST')
        print furl + ' (' + inst + ')'

#Print out the json bug report in a concise and easily readable way.
def pprint(j):
    ty = j.get('by','UNK')
    func = j.get('at_func','UNK_FUNC')
    furl = mkurl(j)
    inst = j.get('instr','UNK_INST')
    #Print heading part: the warned instr and its src location.
    print ty + ' ' + furl + ' (' + func + ' : ' + inst + ')'
    #Print the taint trace to the warned instr.
    trsk = [s for s in j if s.startswith('inst_trace')]
    cnt = 0
    for tr in trsk:
        print '********Trace(%d)********' % cnt
        pprint_trace(j.get(tr,[]))
        cnt += 1
        print ''

def dump_warns_pretty(ty):
    global jwarns
    cnt = 0
    for j in jwarns:
        if j.get('by','').find(ty) < 0:
            continue
        print '=================WARN %d=================' % cnt
        pprint(j)
        cnt += 1

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print 'Usage: ./ext_warns.py log'
    else:
        ext_warns(sys.argv[1])
        #dump_warns_raw()
        dump_warns_pretty('IntegerOverflowDetector')
