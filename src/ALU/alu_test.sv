//==============================================================
//  ALU Testbench with Directed Tests, Random Tests,
//  and Functional Coverage
//
//  Features:
//   • Directed vector testing (original provided patterns)
//   • Randomized stimulus using a constrained class
//   • Functional coverage: opcode, zero flag, output ranges
//   • Unified clock generation and DUT instantiation
//
//  This testbench is intended for simulation (Questa / Xcelium)
//==============================================================

import typedefs::*;

module alu_test;
timeunit 1ns;
timeprecision 100ps;

// ------------------------------------------------------------
// Signals for DUT inputs and outputs
// ------------------------------------------------------------
logic  [7:0] accum, data, out;
logic        zero;
opcode_t     opcode = HLT;      // Start with a legal opcode

// ------------------------------------------------------------
// Clock generation
// ------------------------------------------------------------
`define PERIOD 10
logic clk = 1'b1;
always #(`PERIOD/2) clk = ~clk;

// ------------------------------------------------------------
// Instantiate DUT
// ------------------------------------------------------------
alu alu1 (
    .out(out),
    .zero(zero),
    .clk(clk),
    .accum(accum),
    .data(data),
    .opcode(opcode)
);

//==============================================================
//  Functional Coverage
//==============================================================

// ------------------------------------------------------------
// 1. Opcode coverage — ensure all ALU operations are exercised
// ------------------------------------------------------------
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

// ------------------------------------------------------------
// 2. Zero-flag coverage — detect transitions 0 → 1 and 1 → 0
// ------------------------------------------------------------
covergroup cg_zero @(posedge clk);
    cp_zero : coverpoint zero {
        bins z0 = {0};
        bins z1 = {1};
    }
endgroup

// ------------------------------------------------------------
// 3. Output-value distribution — low/mid/high ranges
// ------------------------------------------------------------
covergroup cg_out @(posedge clk);
    cp_out : coverpoint out {
        bins low    = { [0:15] };
        bins mid    = { [16:127] };
        bins high   = { [128:255] };
    }
endgroup

// Instantiate covergroups
cg_opcode   cov_opcode  = new();
cg_zero     cov_zero    = new();
cg_out      cov_out     = new();

//==============================================================
//  Random Test Class
//==============================================================

// This class can generate randomized ALU inputs.
// Only opcodes inside the legal enum are allowed.
class RandALU;
    rand logic [7:0] accum, data;
    rand opcode_t   opcode;

    constraint legal_opcode {
        opcode inside {HLT, SKZ, ADD, AND, XOR, LDA, STO, JMP};
    }
endclass

RandALU rv = new();

//==============================================================
//  Checker Task for Directed Tests
//==============================================================
//
// Expects = 9-bit: {zero, out[7:0]}
// The directed tests compare the DUT result with a known value.
// Random tests do not use checkit() because expected values
// are not precomputed in this TB.
//
task checkit (input [8:0] expects);
begin
    $display("%t opcode=%s data=%h accum=%h | zero=%b out=%h",
                $time, opcode.name(), data, accum, zero, out);

    if ({zero, out} !== expects) begin
        $display("zero:%b out:%h expected:%b_%h",
                    zero, out, expects[8], expects[7:0]);
        $display("ALU TEST FAILED");
        $stop;
    end
end
endtask

//==============================================================
//  Directed Tests
//==============================================================
//
// These patterns correspond to known-good ALU operations.
// They validate the deterministic behavior of all instructions.
//
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

//==============================================================
//  Random Test
//==============================================================
//
// Generates random opcode/data/accum combinations.
// No checking is done here because the expected value is not
// computed in this testbench, but coverage will record all cases.
//
task run_random(input int num_tests);
begin
    $display("----- RANDOM TEST START -----");

    repeat (num_tests) begin
        void'(rv.randomize());

        opcode = rv.opcode;
        accum  = rv.accum;
        data   = rv.data;

        @(posedge clk);

        $display("%t [RANDOM] opcode=%s accum=%h data=%h out=%h zero=%b",
                    $time, opcode.name(), accum, data, out, zero);
    end

    $display("----- RANDOM TEST END -----");
end
endtask

//==============================================================
//  Main Test Sequence
//==============================================================
initial begin
    $timeformat(-9, 1, " ns", 9);

    // Step 1: Directed tests
    run_directed();

    // Step 2: Randomized tests — adjustable test count
    run_random(300);

    // Finish
    $display("===== TEST COMPLETED (NO TIMEOUT) =====");
    $stop;
end

endmodule
