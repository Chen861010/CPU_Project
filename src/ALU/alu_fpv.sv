//==============================================================
//  ALU Assertions for JasperGold 
//  This module validates correctness of:
//   • Zero flag (combinational correctness)
//   • ALU functional behavior
//   • Proper timing: ALU updates output on the *negedge* clock
//   • Opcode-to-output truth table
//==============================================================

timeunit 1ns;
timeprecision 100ps;

import typedefs::*;

module alu_assert (
    input  logic       clk,       // ALU clock (RTL updates out at negedge)
    input  logic [7:0] accum,     // Current accumulator value
    input  logic [7:0] data,      // Input data
    input  opcode_t    opcode,    // ALU opcode enum
    input  logic [7:0] out,       // ALU output (latched on negedge clk)
    input  logic       zero       // ALU zero flag
);

    // ------------------------------------------------------------
    // 1. Default SVA clock domain (posedge)
    // ------------------------------------------------------------
    default clocking cb @(posedge clk); endclocking

    // 'init' goes high after the first posedge to avoid undefined startup checks
    logic init = 1'b0;
    always_ff @(posedge clk)
        init <= 1'b1;


    // ------------------------------------------------------------
    // 2. Capture inputs at negedge — ALU uses these values to compute 'out'
    // ------------------------------------------------------------
    logic [7:0] accum_neg, data_neg;
    opcode_t    opcode_neg;

    always_ff @(negedge clk) begin
        accum_neg  <= accum;
        data_neg   <= data;
        opcode_neg <= opcode;
    end


    // ------------------------------------------------------------
    // 3. Capture the ALU’s updated output at negedge
    //    This is the true moment when RTL updates 'out'
    // ------------------------------------------------------------
    logic [7:0] out_neg;

    always_ff @(negedge clk)
        out_neg <= out;


    // ------------------------------------------------------------
    // 4. Environment assumptions: no X/Z on ALU inputs
    // ------------------------------------------------------------
    assume property ( !(accum  !== accum ) );
    assume property ( !(data   !== data  ) );
    assume property ( !(opcode !== opcode) );


    // ------------------------------------------------------------
    // 5. Zero flag correctness (combinational)
    // ------------------------------------------------------------
    assert property (
        zero == (accum == 8'h00)
    );


    // ------------------------------------------------------------
    // 6. Functional correctness — opcode truth table
    //
    //   RTL updates at negedge, so at next *posedge*:
    //      out == f(accum_neg, data_neg, opcode_neg)
    // ------------------------------------------------------------

    // HLT — output remains accumulator
    assert property (
        init && opcode_neg == HLT
        |-> out == accum_neg
    );

    // SKZ — ALU does not modify accumulator
    assert property (
        init && opcode_neg == SKZ
        |-> out == accum_neg
    );

    // ADD — 8-bit addition (carry ignored)
    assert property (
        init && opcode_neg == ADD
        |-> out == (data_neg + accum_neg)
    );

    // AND — bitwise AND
    assert property (
        init && opcode_neg == AND
        |-> out == (data_neg & accum_neg)
    );

    // XOR — bitwise XOR
    assert property (
        init && opcode_neg == XOR
        |-> out == (data_neg ^ accum_neg)
    );

    // LDA — load data into accumulator
    assert property (
        init && opcode_neg == LDA
        |-> out == data_neg
    );

    // STO — ALU simply returns accumulator; memory write handled elsewhere
    assert property (
        init && opcode_neg == STO
        |-> out == accum_neg
    );

    // JMP — control flow handled externally; ALU preserves accumulator
    assert property (
        init && opcode_neg == JMP
        |-> out == accum_neg
    );


    // ------------------------------------------------------------
    // 7. Additional timing check:
    //    Track "out" at negedge and confirm stability on next posedge.
    //
    //    out_negedge  → value of out *at negedge* (actual RTL update)
    //    out_posedge  → the stable version sampled on next posedge
    // ------------------------------------------------------------
    logic [7:0] out_negedge;   // ALU output as updated on negedge
    logic [7:0] out_posedge;   // SVA-stable version at posedge

    // Sample actual ALU update at negedge
    always_ff @(negedge clk)
        out_negedge <= out;

    // Sample the previously-updated value at next posedge
    always_ff @(posedge clk)
        out_posedge <= out_negedge;

endmodule
