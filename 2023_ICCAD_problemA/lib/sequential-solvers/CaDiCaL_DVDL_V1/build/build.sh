#!/bin/sh
tar xf ../archives/cadical*
mv cadical* cadical
cd cadical
./configure --competition
make test
install -s build/cadical ../../bin/
