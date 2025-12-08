// ============================================================================
// cpu_assertions.sv  — CPU-Level Behavioral and Control Assertions
// Final Version — Cleaned, Standardized Messages, No Logic Changes
// ============================================================================

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

  // Disable assertions while reset is active
  `define DISABLE_IF_RESET disable iff (!rst_)

  // ==========================================================================
  // 1. ALU instructions must assert load_ac during ALU_OP / STORE
  // ==========================================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (opcode inside {ADD, AND, XOR, LDA} &&
       ps     inside {ALU_OP, STORE})
      |-> load_ac
  ) else $error("ASSERT#1: load_ac must be asserted during ALU operations");

  // ==========================================================================
  // 2. SKZ + zero=1 in ALU_OP must produce inc_pc
  // ==========================================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (opcode == SKZ && zero == 1 && ps == ALU_OP)
        |-> inc_pc
  ) else $error("ASSERT#2: SKZ with zero=1 did not increment PC");

  // ==========================================================================
  // 3. JMP must assert load_pc during ALU_OP / STORE
  // ==========================================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (opcode == JMP && ps inside {ALU_OP, STORE})
        |-> load_pc
  ) else $error("ASSERT#3: JMP must assert load_pc during ALU_OP/STORE");

  // ==========================================================================
  // 4. STO must assert mem_wr during STORE state
  // ==========================================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (opcode == STO && ps == STORE)
        |-> mem_wr
  ) else $error("ASSERT#4: STO did not assert mem_wr in STORE");

  // ==========================================================================
  // 5. Illegal combination: load_pc and inc_pc cannot be 1 simultaneously
  //    (Exception: JMP during STORE)
  // ==========================================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      !(load_pc && inc_pc && !(opcode == JMP && ps == STORE))
  ) else $error("ASSERT#5: Illegal combination: load_pc & inc_pc both active");

  // ==========================================================================
  // 6. JMP must NOT assert load_pc early (OP_ADDR / OP_FETCH)
  // ==========================================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (opcode == JMP && ps inside {OP_ADDR, OP_FETCH})
        |-> !load_pc
  ) else $error("ASSERT#6: JMP load_pc asserted too early");

  // ==========================================================================
  // 7. HLT instruction must assert halt in OP_ADDR
  // ==========================================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (ps == OP_ADDR && opcode == HLT)
        |-> halt
  ) else $error("ASSERT#7: HLT did not assert halt in OP_ADDR");

  // ==========================================================================
  // 8. INST_LOAD and IDLE must assert load_ir
  // ==========================================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (ps inside {INST_LOAD, IDLE})
        |-> load_ir
  ) else $error("ASSERT#8: load_ir not asserted in INST_LOAD/IDLE");

  // ==========================================================================
  // 9. PC update signals must be one-hot (except STORE+JMP case)
  // ==========================================================================
  assert property(`DISABLE_IF_RESET
    @(posedge clk)
      (ps inside {OP_ADDR, ALU_OP})
        |-> $onehot0({inc_pc, load_pc})
  ) else $error("ASSERT#9: PC update signals are not one-hot");

endmodule
