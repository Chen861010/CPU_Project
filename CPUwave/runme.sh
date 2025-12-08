#!/bin/tcsh

source xrun.cshrc
xrun typedefs.sv cpu_tb.sv cpu.sv Mem.sv ALU.sv \
     8S_control.sv 8bit_rig.sv 5bit_count.sv 2to1_mux.sv \
     -access +rwc -gui
