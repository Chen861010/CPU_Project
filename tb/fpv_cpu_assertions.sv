// =============================================================
// cpu_assertions.sv  (FINAL — verified against control.sv behavior)
// =============================================================
timeunit 1ns;
timeprecision 100ps;

import typedefs::*;

module cpu_assertions (
    input logic clk,
    input logic rst_,
    input opcode_t opcode,
    input state_t  ps,
    input logic load_ac,
    input logic load_pc,
    input logic inc_pc,
    input logic zero,
    input logic mem_wr,
    input logic halt,
    input logic load_ir
);

  // Helper: disable during reset
  `define DISABLE_IF_RESET disable iff (!rst_)

  // ============================================================
  // 1. ALU 指令 → 在 ALU_OP / STORE 必須 assert load_ac
  // ============================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (opcode inside {ADD, AND, XOR, LDA} &&
       ps     inside {ALU_OP, STORE})
      |-> load_ac
  ) else $error("ASSERT#1: load_ac missing during ALU instructions");

  // ============================================================
  // 2. SKZ → zero=1 & ps=ALU_OP 必須 inc_pc
  // ============================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (opcode == SKZ && zero == 1 && ps == ALU_OP)
        |-> inc_pc
  ) else $error("ASSERT#2: SKZ did not produce inc_pc");

  // ============================================================
  // 3. JMP → 在 ALU_OP / STORE 必須 assert load_pc
  // ============================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (opcode == JMP && ps inside {ALU_OP, STORE})
        |-> load_pc
  ) else $error("ASSERT#3: load_pc missing during JMP");

  // ============================================================
  // 4. STO → STORE 必須 assert mem_wr
  // ============================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (opcode == STO && ps == STORE)
        |-> mem_wr
  ) else $error("ASSERT#4: STO missing mem_wr");

  // ============================================================
  // 5. 禁止 load_pc & inc_pc 同時為 1（僅 JMP in STORE 是合法）
  // ============================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      !(load_pc && inc_pc && !(opcode == JMP && ps == STORE))
  ) else $error("ASSERT#5: Illegal inc_pc + load_pc combination");

  // ============================================================
  // 6. JMP 在 OP_ADDR / OP_FETCH 不可產生 load_pc
  // ============================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (opcode == JMP && ps inside {OP_ADDR, OP_FETCH})
        |-> !load_pc
  ) else $error("ASSERT#6: JMP load_pc too early");

  // ============================================================
  // 7. HLT → 在 OP_ADDR 必須 assert halt
  // ============================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (ps == OP_ADDR && opcode == HLT)
        |-> halt
  ) else $error("ASSERT#7: HLT missing halt signal");

  // ============================================================
  // 8. INST_LOAD → 必須 assert load_ir
  //    IDLE 也必須 load_ir（spec 表格有顯示）
  // ============================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (ps inside {INST_LOAD, IDLE})
        |-> load_ir
  ) else $error("ASSERT#8: load_ir missing in INST_LOAD/IDLE");

  // ============================================================
  // 9. PC update one-hot（STORE 除外；STORE+JMP 會兩個一起 1）
  // ============================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (ps inside {OP_ADDR, ALU_OP})
        |-> $onehot0({inc_pc, load_pc})
  ) else $error("ASSERT#9: PC update is not one-hot");

endmodule
