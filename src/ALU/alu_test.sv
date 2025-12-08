import typedefs::*;

module alu_test;
timeunit 1ns;
timeprecision 100ps;

logic  [7:0] accum, data, out;
logic  zero;
opcode_t opcode = HLT;

// Clock
`define PERIOD 10
logic clk = 1'b1;
always #(`PERIOD/2) clk = ~clk;

// DUT
alu alu1 (
    .out(out),
    .zero(zero),
    .clk(clk),
    .accum(accum),
    .data(data),
    .opcode(opcode)
);

// ------------------------------------------------------------
// =============== NEW : Coverage Groups ======================
// ------------------------------------------------------------

// 1. opcode coverage
covergroup cg_opcode @(posedge clk);
    cp_opcode : coverpoint opcode {
        bins HLT = {HLT};
        bins SKZ = {SKZ};
        bins ADD = {ADD};
        bins AND = {AND};
        bins XOR = {XOR};
        bins LDA = {LDA};
        bins STO = {STO};
        bins JMP = {JMP};
    }
endgroup

// 2. zero flag coverage
covergroup cg_zero @(posedge clk);
    cp_zero : coverpoint zero { bins z0 = {0}; bins z1 = {1}; }
endgroup

// 3. output value spread coverage
covergroup cg_out @(posedge clk);
    cp_out : coverpoint out {
        bins low    = { [0:15] };
        bins mid    = { [16:127] };
        bins high   = { [128:255] };
    }
endgroup

cg_opcode   cov_opcode  = new();
cg_zero     cov_zero    = new();
cg_out      cov_out     = new();

// ------------------------------------------------------------
// =============== NEW : Random Test Class ====================
// ------------------------------------------------------------
class RandALU;
    rand logic [7:0] accum, data;
    rand opcode_t   opcode;

    // 避免無意義的 case，例如 SKZ/HLT 無運算 → 不限制但可加入更多 constraints
    constraint legal_opcode { opcode inside {HLT,SKZ,ADD,AND,XOR,LDA,STO,JMP}; }

endclass

RandALU rv = new();

// ------------------------------------------------------------
// =============== Checker Task (原本的) ========================
// ------------------------------------------------------------
task checkit (input [8:0] expects);
begin
    $display("%t opcode=%s data=%h accum=%h | zero=%b out=%h",
                $time, opcode.name(), data, accum, zero, out);
    if ({zero, out} !== expects)
    begin
        $display("zero:%b out:%b expected:%b_%b",
                    zero, out, expects[8], expects[7:0]);
        $display("ALU TEST FAILED");
        $stop;
    end
end
endtask

// ------------------------------------------------------------
// =============== Directed Tests (原本保留) =====================
// ------------------------------------------------------------
task run_directed;
begin
    @(posedge clk)
    { opcode, data, accum } = 19'h0_37_DA; @(posedge clk) checkit('h0_da);
    { opcode, data, accum } = 19'h1_37_DA; @(posedge clk) checkit('h0_da);
    { opcode, data, accum } = 19'h2_37_DA; @(posedge clk) checkit('h0_11);
    { opcode, data, accum } = 19'h3_37_DA; @(posedge clk) checkit('h0_12);
    { opcode, data, accum } = 19'h4_37_DA; @(posedge clk) checkit('h0_ed);
    { opcode, data, accum } = 19'h5_37_DA; @(posedge clk) checkit('h0_37);
    { opcode, data, accum } = 19'h6_37_DA; @(posedge clk) checkit('h0_da);
    { opcode, data, accum } = 19'h7_37_00; @(posedge clk) checkit('h1_00);
    { opcode, data, accum } = 19'h2_07_12; @(posedge clk) checkit('h0_19);
    { opcode, data, accum } = 19'h3_1F_35; @(posedge clk) checkit('h0_15);
    { opcode, data, accum } = 19'h4_1E_1D; @(posedge clk) checkit('h0_03);
    { opcode, data, accum } = 19'h5_72_00; @(posedge clk) checkit('h1_72);
    { opcode, data, accum } = 19'h6_00_10; @(posedge clk) checkit('h0_10);

    $display("DIRECTED TEST PASSED");
end
endtask

// ------------------------------------------------------------
// =============== NEW : Random Test ===========================
// ------------------------------------------------------------
// 可修改測試次數：num_tests
task run_random(input int num_tests);
begin
    $display("----- RANDOM TEST START -----");

    repeat (num_tests) begin
        void'(rv.randomize());

        opcode = rv.opcode;
        accum  = rv.accum;
        data   = rv.data;

        @(posedge clk);

        // 不做 checkit → 因為沒有 expected 值
        // 但會收 coverage
        $display("%t [RANDOM] opcode=%s accum=%h data=%h out=%h zero=%b",
                    $time, opcode.name(), accum, data, out, zero);
    end

    $display("----- RANDOM TEST END -----");
end
endtask


// ------------------------------------------------------------
// =============== Main Test Flow =============================
// ------------------------------------------------------------
initial begin
    $timeformat(-9, 1, " ns", 9);

    // 1. Directed tests first
    run_directed();

    // 2. Random test (修改次數)
    run_random(300);   // 你想 1000 也可以 run_random(1000)

    // 結束印出覆蓋率（questa/cadence 都支援）
    $display("===== TEST COMPLETED (NO TIMEOUT) =====");
    $stop;
end

endmodule
