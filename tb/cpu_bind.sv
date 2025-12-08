import typedefs::*;

bind cpu cpu_assertions assert_inst (
    .clk      (clk),
    .rst_     (rst_),
    .opcode   (opcode),
    .ps       (cntl.ps),
    .load_ac  (load_ac),
    .load_pc  (load_pc),
    .inc_pc   (inc_pc),
    .zero     (zero),
    .mem_wr   (mem_wr),
    .halt     (halt),
    .load_ir  (load_ir)
);



