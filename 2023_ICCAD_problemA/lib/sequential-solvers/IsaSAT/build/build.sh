#!/bin/sh
# compilation flag
echo "extracting and moving archive"
tar xf ../archives/isasat*
mv isasat* isasat
cd isasat/src
# enable clang on starexec
echo "activating llvm & running make"
scl enable llvm-toolset-7.0 'make competition'
install -s isasat ../../../bin/isasat
