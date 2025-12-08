clear -all

analyze -sv \
    2to1_mux.sv \
    mux_fpv.sv \
    mux_bind.sv

elaborate -top scale_mux

prove -all

