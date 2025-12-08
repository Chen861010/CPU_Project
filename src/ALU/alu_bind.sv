//==============================================================
//  alu_bind.sv - Bind Assertions to DUT
//==============================================================
import typedefs::*;

bind alu alu_assert alu_assert_inst (
    .clk(clk),
    .accum(accum),
    .data(data),
    .opcode(opcode),
    .out(out),
    .zero(zero)
);

