#!/bin/bash
#To run the Dr.Checker static analysis (pointer and taint) module
#$1: ".bc" file
#$2: entry function name/entry config file

func_type="MY_IOCTL"
if (($# > 2))
then
    for ((i=3;i<=$#;i++))
    do
        func_type=${func_type}_${!i}
    done
fi
echo $func_type

conf_name=`basename $2`
#nohup opt -load build_dir/SoundyAliasAnalysis/libSoundyAliasAnalysis.so -dr_checker -toCheckFunction=$2 -functionType=$func_type -outputFile=$2.warn.json -instrWarnings=$2.iwarn.json $1 -o /dev/null >log_$2 2>&1 &
nohup opt -load build_dir/SoundyAliasAnalysis/libSoundyAliasAnalysis.so -dr_checker -entryConfig=$2 -outputFile=$2.warn.json -instrWarnings=$2.iwarn.json $1 -o /dev/null >$2.log 2>&1 &
