#!/bin/sh
tar xf ../archive/kissat*
mv kissat* kissat
cd kissat
./configure --competition --test
make all || exit 1
build/tissat || exit 1
exec install -s build/kissat ../../bin/
