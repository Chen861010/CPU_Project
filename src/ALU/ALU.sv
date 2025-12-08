timeunit 1ns;
timeprecision 100ps;

import typedefs::*;      // Imports opcode_t (3-bit enum) and other shared typedefs

module alu (
    input  logic        clk,        // Clock input (ALU updates on the negative edge)
    input  logic [7:0]  accum,      // Current accumulator value
    input  logic [7:0]  data,       // Data input (from memory or other source)
    input  opcode_t     opcode,     // 3-bit ALU opcode encoded as an enum
    output logic [7:0]  out,        // ALU output (latched on negedge clk)
    output logic        zero        // Zero flag (combinational, based on 'accum')
);

    // ------------------------------------------------------------
    // Zero flag logic (combinational)
    // ------------------------------------------------------------
    // The zero flag is asserted when the accumulator equals 0.
    // It is fully combinational and does not depend on clocking.
    always_comb begin
        zero = (accum == 8'h00);
    end

    // ------------------------------------------------------------
    // Combinational ALU computation
    // ------------------------------------------------------------
    // out_next holds the computed result for the current opcode.
    // The value is latched into 'out' on the falling clock edge.
    logic [7:0] out_next;

    always_comb begin
        // Default: most instructions simply pass through the accumulator.
        // Setting a default value avoids unintended latch inference.
        out_next = accum;

        unique case (opcode)
            HLT: out_next = accum;               // 000: Halt — ALU output remains unchanged
            SKZ: out_next = accum;               // 001: Skip-if-zero — skip behavior handled by controller
            ADD: out_next = data + accum;        // 010: 8-bit addition (carry is ignored)
            AND: out_next = data & accum;        // 011: Bitwise AND
            XOR: out_next = data ^ accum;        // 100: Bitwise XOR
            LDA: out_next = data;                // 101: Load accumulator with data
            STO: out_next = accum;               // 110: Store instruction — write to memory resolved elsewhere
            JMP: out_next = accum;               // 111: Jump — branching handled by controller
            default: /* retain default value */ ;
        endcase
    end

    // ------------------------------------------------------------
    // Sequential logic
    // ------------------------------------------------------------
    // The ALU output is updated only at the *falling* edge of clk.
    // This models the textbook ALU timing used in the VeriRisc CPU.
    always_ff @(negedge clk) begin
        out <= out_next;
    end

endmodule
