#!/bin/tcsh

source xrun.cshrc

# ????
xrun  8bit_rig.sv register_test.sv \
     -access +rwc -gui
