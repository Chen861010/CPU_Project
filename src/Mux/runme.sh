#!/bin/tcsh

source xrun.cshrc
xrun 2to1_mux.sv scale_mux_test.sv\
     -access +rwc -gui
