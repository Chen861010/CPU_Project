timeunit 1ns;
timeprecision 100ps;

import typedefs::*;      // 你的 Controller lab 裡的 package（內含 opcode_t 的 enum）

module alu (
    input  logic        clk,
    input  logic [7:0]  accum,
    input  logic [7:0]  data,
    input  opcode_t     opcode,   // 3-bit enum from typedefs.sv
    output logic [7:0]  out,
    output logic        zero
);

    // 非同步 zero：只取決於 accum
    always_comb begin
        zero = (accum == 8'h00);
    end

    // 組合邏輯：決定下一個 out 值（在負緣鎖存）
    logic [7:0] out_next;

    always_comb begin
        // 預設值避免 latch；題目多數情況都回傳 accum
        out_next = accum;

        unique case (opcode)
            HLT: out_next = accum;           // 000
            SKZ: out_next = accum;           // 001   (真正是否跳過由控制器決定，ALU 仍輸出 accum)
            ADD: out_next = data + accum;    // 010   8-bit 加總，忽略進位
            AND: out_next = data & accum;    // 011
            XOR: out_next = data ^ accum;    // 100
            LDA: out_next = data;            // 101
            STO: out_next = accum;           // 110   (實際寫回記憶體由其他模組處理)
            JMP: out_next = accum;           // 111   (是否跳轉由控制器決定)
            default: /* keep default */ ;
        endcase
    end

    // 時序邏輯：在 clk 負緣更新 out
    always_ff @(negedge clk) begin
        out <= out_next;
    end

endmodule