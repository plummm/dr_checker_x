#!/bin/bash

clang $1.c -emit-llvm -c -O1 -o $1.bc
llvm-dis $1.bc -o $1.ll
