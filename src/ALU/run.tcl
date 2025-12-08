clear -all

analyze -sv \
    typedefs.sv \
    ALU.sv \
    alu_fpv.sv \
    alu_bind.sv
elaborate -top alu

clock clk -both_edges
reset -none

prove -all

