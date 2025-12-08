import typedefs::*;

bind control control_assertions CTRL_ASSERT (
    .clk     (clk),
    .rst_    (rst_),
    .opcode  (opcode),
    .ps      (state),    
    .zero    (zero),

    .load_ac (load_ac),
    .mem_rd  (mem_rd),
    .mem_wr  (mem_wr),
    .inc_pc  (inc_pc),
    .load_pc (load_pc),
    .load_ir (load_ir),
    .halt    (halt)
);

