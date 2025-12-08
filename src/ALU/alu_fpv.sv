//==============================================================
//  ALU Assertions for JasperGold (Shadow negedge version)
//==============================================================

timeunit 1ns;
timeprecision 100ps;

import typedefs::*;

module alu_assert (
    input  logic       clk,
    input  logic [7:0] accum,
    input  logic [7:0] data,
    input  opcode_t    opcode,
    input  logic [7:0] out,
    input  logic       zero
);

    // ------------------------------------------------------------
    // 1. Default SVA clock (posedge)
    // ------------------------------------------------------------
    default clocking cb @(posedge clk); endclocking

    logic init = 1'b0;
    always_ff @(posedge clk)
        init <= 1'b1;


    // ------------------------------------------------------------
    // 2. Shadow the inputs at negedge (ALU updates out on negedge)
    // ------------------------------------------------------------
    logic [7:0] accum_neg, data_neg;
    opcode_t    opcode_neg;

    always_ff @(negedge clk) begin
        accum_neg  <= accum;
        data_neg   <= data;
        opcode_neg <= opcode;
    end


    // ------------------------------------------------------------
    // 3. Shadow the *new* ALU output at negedge
    //    → This correctly captures the version that the RTL writes.
    // ------------------------------------------------------------
    logic [7:0] out_neg;

    always_ff @(negedge clk) begin
        out_neg <= out;   // record updated out value
    end


    // ------------------------------------------------------------
    // Environment assumptions (no X/Z)
    // ------------------------------------------------------------
    assume property ( !(accum  !== accum ) );
    assume property ( !(data   !== data  ) );
    assume property ( !(opcode !== opcode) );


    // ------------------------------------------------------------
    // 4. ZERO flag correctness (asynchronous)
    // ------------------------------------------------------------
    assert property (
        zero == (accum == 8'h00)
    );


    // ------------------------------------------------------------
    // 5. Functional correctness (match table)
    //
    //    out is updated on negedge, so at next posedge:
    //       out == f(accum_neg, data_neg)
    // ------------------------------------------------------------

    // HLT
    assert property (
        init && opcode_neg == HLT
        |-> out == accum_neg
    );

    // SKZ
    assert property (
        init && opcode_neg == SKZ
        |-> out == accum_neg
    );

    // ADD
    assert property (
        init && opcode_neg == ADD
        |-> out == (data_neg + accum_neg)
    );

    // AND
    assert property (
        init && opcode_neg == AND
        |-> out == (data_neg & accum_neg)
    );

    // XOR
    assert property (
        init && opcode_neg == XOR
        |-> out == (data_neg ^ accum_neg)
    );

    // LDA
    assert property (
        init && opcode_neg == LDA
        |-> out == data_neg
    );

    // STO
    assert property (
        init && opcode_neg == STO
        |-> out == accum_neg
    );

    // JMP
    assert property (
        init && opcode_neg == JMP
        |-> out == accum_neg
    );
    logic [7:0] out_negedge;   // 在 negedge 記錄 RTL out
    logic [7:0] out_posedge;   // 在 posedge 紀錄 “上一個 negedge 的 out”

    // 取得 negedge 的 out（真正發生更新的地方）
    always_ff @(negedge clk)
        out_negedge <= out;

    // 取得 “上一個 negedge 的 out” 的穩定版本（在 posedge）
    always_ff @(posedge clk)
        out_posedge <= out_negedge;

endmodule
