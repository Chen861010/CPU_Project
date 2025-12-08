#!/bin/tcsh

source xrun.cshrc


xrun typedefs.sv ALU.sv \
     alu_test.sv \
     -access +rwc -gui
