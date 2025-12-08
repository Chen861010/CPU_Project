clear -all

analyze -sv \
    typedefs.sv \
    2to1_mux.sv \
    5bit_count.sv \
    8bit_rig.sv \
    8S_control.sv \
    ALU.sv \
    Mem.sv \
    cpu.sv \
    fpv_cpu_assertions.sv \
    cpu_bind.sv

elaborate -top cpu

clock clk
reset ~rst_

prove -all

