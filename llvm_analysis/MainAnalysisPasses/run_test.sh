#!/bin/bash
#To run the Dr.Checker static analysis (pointer and taint) module
#$1: ".bc" file
#$2: entry function name

nohup opt -load build_dir/SoundyAliasAnalysis/libSoundyAliasAnalysis.so -dr_checker -toCheckFunction=$2 -functionType="NULL_ARG" -outputFile="dr.out.json" $1 -o /dev/null >log_test 2>&1 &
