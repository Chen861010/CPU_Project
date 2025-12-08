#!/bin/sh
# Compile with coverage enabled
vlog 8bit_rig.sv
vlog register_test.sv +fcover -cover sbceft +cover=f -O0  

# Run simulation in command-line mode with coverage enabled
vsim work.register_test -coverage +acc -c -do cover.do


