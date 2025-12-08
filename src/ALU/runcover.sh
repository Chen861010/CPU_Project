#!/bin/sh
# Compile with coverage enabled
vlog typedefs.sv
vlog ALU.sv
vlog alu_test.sv +fcover -cover sbceft +cover=f -O0  

# Run simulation in command-line mode with coverage enabled
vsim work.alu_test -coverage +acc -c -do cover.do



