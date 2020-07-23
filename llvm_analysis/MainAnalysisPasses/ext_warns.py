#!/usr/bin/python

#Extract and process the warnings in the log output.

import sys,os

warns = []

def ext_warns(log):
    global warns
    is_warn = False
    with open(log,'r') as f:
        for l in f:
            if l.startswith('@@@@@@'):
                is_warn = (not is_warn)
            elif is_warn:
                #One line per warning.
                warns.append(l.strip())
    #TODO: Do some filtering, grouping, etc according to the warning json content.
    #Dump the warning
    for l in warns:
        print l

if __name__ == '__main__':
    if len(sys.argv) < 2:
        print 'Usage: ./ext_warns.py log'
    else:
        ext_warns(sys.argv[1])
