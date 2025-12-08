#!/bin/sh
# Compile with coverage enabled
vlog 2to1_mux.sv
vlog scale_mux_test.sv +fcover -cover sbceft +cover=f -O0  

# Run simulation in command-line mode with coverage enabled
vsim work.scale_mux_test -coverage +acc -c -do cover.do

