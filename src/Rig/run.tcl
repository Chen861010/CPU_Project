clear -all

analyze -sv \
    rig_fpv.sv \
    8bit_rig.sv \
    rig_bind.sv

elaborate -top register

clock clk
reset ~rst_

prove -all

