#!/usr/bin/python

import sys,os

FUNC_NAME_LEN_MAX = 48

def ext_time_sec(l):
    l = l.strip()
    tks = l.split(" ")
    try:
        return float(tks[-1][:-1])
    except:
        print 'Invalid line to extract time duration: ' + l;
        return None

def print_array_info(arr,detail=False):
    arr.sort(reverse=True)
    n = len(arr)
    s = sum(arr)
    avg = float(s)/float(n)
    print 'sum: %-*f Len: %-*d Avg: %f' % (12,s,6,n,avg)
    if detail:
        tenths = [arr[i] for i in range(0,n,n/10)]
        ratios = [sum([arr[j] for j in range(i,min(i+n/10,n))])/s for i in range(0,n,n/10)]
        head = [arr[i] for i in range(min(10,n))]
        tail = [arr[i] for i in range(max(-10,0-n),0)]
        print 'Tenths: ' + str(tenths)
        print 'Ratios: ' + str(ratios)
        print '  Head: ' + str(head)
        print '  Tail: ' + str(tail)
    return [n,s,avg]

def time_analysis(tl):
    t_inst = {
        'visitLoadInst' : [],
        'visitStoreInst' : [],
        'visitGetElementPtrInst' : [],
    }
    ft = {}
    with open(tl,'r') as f:
        for l in f:
            if not l.startswith('[TIMING]'):
                continue
            if l.find('End func') >= 0:
                #Statistics about the function analysis time.
                #E.g. 
                #[TIMING] End func(5) svm_has_high_real_mode_segbase in: 121127
                #Get the func name and its call depth
                tks = l.split(' ')
                ls = l[l.find('(')+1 : l.find(')')]
                if not ls.isdigit() or len(tks) < 6:
                    print 'Invalid line to time a function execution: ' + l
                    continue
                level = int(ls)
                nm = tks[3]
                t = ext_time_sec(l)
                ft.setdefault(level,{}).setdefault(nm,[])
                ft[level][nm] += [t]
            else:
                #Statistics about the inst analysis time.
                for ki in t_inst:
                    if l.find(ki) >= 0:
                        t = ext_time_sec(l)
                        if t:
                            t_inst[ki] += [t]
    #Ok, it's the time to show the statistics.
    #For insts:
    print '=============INSTS============='
    for ki in t_inst:
        print '===== %-*s:' % (20,ki),
        print_array_info(t_inst[ki],True)
    #For funcs:
    f_cnt = {}
    print '=============FUNCS============='
    for lvl in sorted(ft.keys()):
        print '======== LEVEL: ' + str(lvl)
        names = sorted(ft[lvl].keys(),key=lambda x:sum(ft[lvl][x]),reverse=True)
        for nm in names:
            print '%-*s' % (FUNC_NAME_LEN_MAX,nm),
            [n,s,avg] = print_array_info(ft[lvl][nm])
            [on,oavg] = f_cnt.setdefault(nm,[0,0.0]) 
            f_cnt[nm] = [n+on,(float(n)*avg+float(on)*oavg)/float(n+on)]
    print '=============DUPLICATED FUNCS============='
    total = 0.0
    dcnt = 0
    for nm in sorted(f_cnt.keys(),key = lambda x : f_cnt[x][0]*f_cnt[x][1]):
        [n,avg] = f_cnt[nm]
        if n > 1:
            dcnt += 1
            print '%-*s cnt: %-*d avg: %-*f total: %-*f' % (FUNC_NAME_LEN_MAX,nm,5,n,12,avg,12,n*avg)
            total += float(n-1)*avg
    print 'Ratio: %d/%d' % (dcnt,len(f_cnt))
    print 'Total Extra Cost Compared to Bottom-Up: ' + str(total) + 's'

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print 'Usage: ./time.py time_log'
    else:
        time_analysis(sys.argv[1])
