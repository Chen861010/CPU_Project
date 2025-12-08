//==============================================================
//  scale_mux.sv — Parameterized 2-to-1 Multiplexer
//
//  Description:
//    A simple combinational multiplexer with a parameterizable
//    data width. When sel_a is high, the output selects in_a;
//    otherwise, it selects in_b.
//
//  Parameters:
//    WIDTH — bit-width of the input and output signals
//
//  Ports:
//    in_a  — first input operand
//    in_b  — second input operand
//    sel_a — select line (1 → choose in_a, 0 → choose in_b)
//    out   — multiplexed output
//==============================================================

timeunit 1ns;
timeprecision 100ps;

module scale_mux #(parameter int WIDTH = 8) (
    input  logic [WIDTH-1:0] in_a,   // Input A
    input  logic [WIDTH-1:0] in_b,   // Input B
    input  logic             sel_a,  // Select: 1 selects in_a, 0 selects in_b
    output logic [WIDTH-1:0] out     // Multiplexer output
);

    // ------------------------------------------------------------
    // Combinational selection logic
    // ------------------------------------------------------------
    always_comb begin
        out = sel_a ? in_a : in_b;
    end

endmodule
