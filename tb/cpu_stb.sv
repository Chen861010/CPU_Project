// ===============================================================
// cpu_stb.sv — FULL SYSTEM TESTBENCH (Test1–9 + NEW Test4_memwr)
// 
// This testbench provides:
//   • Clock-generation system (master clock + derived clocks)
//   • Directed test programs (CPUtest1–3)
//   • Additional functional tests (Test4–8)
//   • Randomized program generator (Test9)
//   • Full functional and cross coverage collection
//   • Automatic halt detection + PC checking
//   • Assertion binding for CPU-level formal checks
// ===============================================================

timeunit 1ns;
timeprecision 100ps;

import typedefs::*;
`include "cpu_coverage.sv"
import cpu_cov_pkg::*;

module testbench;

  // =============================================================
  // TEST SELECTION CONTROL
  // =============================================================
  localparam int TEST_ALL = 0;
  localparam int TEST_1   = 1;
  localparam int TEST_2   = 2;
  localparam int TEST_3   = 3;
  localparam int TEST_4   = 4;   // Dedicated STO/mem_wr coverage
  localparam int TEST_5   = 5;
  localparam int TEST_6   = 6;
  localparam int TEST_7   = 7;
  localparam int TEST_8   = 8;
  localparam int TEST_9   = 9;

  int TEST_SELECTION = TEST_ALL;

  // Number of iterations for random program test
  int RANDOM_TEST_COUNT = 1000;


  // =============================================================
  // CLOCK GENERATION SYSTEM
  // Master clock → divided clocks for CPU
  // =============================================================
  logic clk, cntrl_clk, alu_clk, fetch;
  logic rst_;
  logic halt;
  logic load_ir;

  `define PERIOD 10
  logic master_clk = 1'b1;
  logic [3:0] count;

  always #(`PERIOD/2) master_clk = ~master_clk;

  // Clock divider (from project specification)
  always @(posedge master_clk or negedge rst_) begin
    if (!rst_) count <= 4'b0;
    else       count <= count + 1;
  end

  assign cntrl_clk = ~count[0];        // Controller FSM clock
  assign clk       = count[1];         // Main CPU clock
  assign fetch     = ~count[3];        // Determines PC vs IR address mux
  assign alu_clk   = ~(count == 4'hC); // ALU negative-edge latch clock


  // =============================================================
  // DUT INSTANTIATION
  // =============================================================
  cpu dut (
      .halt      (halt),
      .load_ir   (load_ir),
      .clk       (clk),
      .cntrl_clk (cntrl_clk),
      .alu_clk   (alu_clk),
      .fetch     (fetch),
      .rst_      (rst_)
  );


  // =============================================================
  // COVERAGE GROUP INSTANTIATION
  // =============================================================
  cg_opcode        cov_opcode      = new;
  cg_control       cov_control     = new;
  cg_pc            cov_pc          = new;
  cg_opcode_ctrl   cov_opcode_ctrl = new;
  cg_skz           cov_skz         = new;
  cg_pc_action     cov_pc_action   = new;
  cg_state         cov_state       = new;
  cg_memwr         cov_mem_wr      = new;

  initial begin
    cov_opcode.start();
    cov_control.start();
    cov_pc.start();
    cov_opcode_ctrl.start();
    cov_skz.start();
    cov_pc_action.start();
    cov_state.start();
    cov_mem_wr.start();
  end


  // =============================================================
  // RESET SEQUENCE
  // =============================================================
  task automatic do_reset();
    rst_ = 0;
    repeat (5) @(posedge master_clk);
    rst_ = 1;
    repeat (5) @(posedge master_clk);
  endtask


  // =============================================================
  // DIRECT MEMORY WRITE (bypassing control & timing)
  // Used to pre-load test programs
  // =============================================================
  task automatic mem_write(input int idx, input [7:0] val);
    dut.mem1.memory[idx] = val;
  endtask


  // =============================================================
  // RUN CPU UNTIL HALT (with cycle timeout)
  // Used by all test programs
  // =============================================================
  task automatic run_until_halt(input int max_cycles,
                                output int final_pc);
    int cycles = 0;
    while (!halt && cycles < max_cycles) begin
      @(posedge clk);
      cycles++;
    end
    final_pc = dut.pc_addr;
  endtask


// =============================================================
// TEST 1 — Official CPUtest1 Program
// =============================================================
  task automatic load_test1();
    int i;
    for (i = 0; i < 32; i++) mem_write(i, 8'h00);

    // Test program body (from specification)
    mem_write(8'h00, 8'b111_11110);
    mem_write(8'h01, 8'h00);
    mem_write(8'h02, 8'h00);
    mem_write(8'h03, 8'b101_11010);
    mem_write(8'h04, 8'b001_00000);
    mem_write(8'h05, 8'h00);
    mem_write(8'h06, 8'b101_11011);
    mem_write(8'h07, 8'b001_00000);
    mem_write(8'h08, 8'b111_01010);
    mem_write(8'h09, 8'h00);
    mem_write(8'h0A, 8'b110_11100);
    mem_write(8'h0B, 8'b101_11010);
    mem_write(8'h0C, 8'b110_11100);
    mem_write(8'h0D, 8'b101_11100);
    mem_write(8'h0E, 8'b001_00000);
    mem_write(8'h0F, 8'h00);
    mem_write(8'h10, 8'b100_11011);
    mem_write(8'h11, 8'b001_00000);
    mem_write(8'h12, 8'b111_10100);
    mem_write(8'h13, 8'h00);
    mem_write(8'h14, 8'b100_11011);
    mem_write(8'h15, 8'b001_00000);
    mem_write(8'h16, 8'h00);
    mem_write(8'h17, 8'h00);
    mem_write(8'h18, 8'b111_00000);

    // Data section
    mem_write(8'h1A, 8'h00);
    mem_write(8'h1B, 8'hFF);
    mem_write(8'h1C, 8'hAA);
    mem_write(8'h1E, 8'b111_00011);
    mem_write(8'h1F, 8'h00);
  endtask


// =============================================================
// TEST 2 — Official CPUtest2 Program
// =============================================================
  task automatic load_test2();
    int i;
    for (i = 0; i < 32; i++) mem_write(i, 8'h00);

    mem_write(8'h00, 8'b101_11011);
    mem_write(8'h01, 8'b011_11100);
    mem_write(8'h02, 8'b100_11011);
    mem_write(8'h03, 8'b001_00000);
    mem_write(8'h04, 8'h00);
    mem_write(8'h05, 8'b010_11010);
    mem_write(8'h06, 8'b001_00000);
    mem_write(8'h07, 8'b111_01001);
    mem_write(8'h08, 8'h00);
    mem_write(8'h09, 8'b100_11100);
    mem_write(8'h0A, 8'b010_11010);
    mem_write(8'h0B, 8'b110_11101);
    mem_write(8'h0C, 8'b101_11010);
    mem_write(8'h0D, 8'b010_11101);
    mem_write(8'h0E, 8'b001_00000);
    mem_write(8'h0F, 8'h00);
    mem_write(8'h10, 8'h00);
    mem_write(8'h11, 8'b111_00000);

    mem_write(8'h1A, 8'h01);
    mem_write(8'h1B, 8'hAA);
    mem_write(8'h1C, 8'hFF);
    mem_write(8'h1D, 8'h00);
  endtask


// =============================================================
// TEST 3 — Official CPUtest3 Program
// =============================================================
  task automatic load_test3();
    int i;
    for (i = 0; i < 32; i++) mem_write(i, 8'h00);

    mem_write(8'h00, 8'b111_00011);
    mem_write(8'h03, 8'b101_11011);
    mem_write(8'h04, 8'b110_11100);
    mem_write(8'h05, 8'b010_11010);
    mem_write(8'h06, 8'b110_11011);
    mem_write(8'h07, 8'b101_11100);
    mem_write(8'h08, 8'b110_11010);
    mem_write(8'h09, 8'b100_11101);
    mem_write(8'h0A, 8'b001_00000);
    mem_write(8'h0B, 8'b111_00011);
    mem_write(8'h0C, 8'h00);
    mem_write(8'h0D, 8'b101_11111);
    mem_write(8'h0E, 8'b110_11010);
    mem_write(8'h0F, 8'b101_11110);
    mem_write(8'h10, 8'b110_11011);
    mem_write(8'h11, 8'b111_00011);

    mem_write(8'h1A, 8'h01);
    mem_write(8'h1B, 8'h00);
    mem_write(8'h1C, 8'h00);
    mem_write(8'h1D, 8'h90);
    mem_write(8'h1E, 8'h00);
    mem_write(8'h1F, 8'h01);
  endtask


// =============================================================
// TEST 4 — New Dedicated STO Test (guarantees mem_wr coverage)
// =============================================================
  task automatic load_test4();
    int i;
    // Clear memory first
    for (i = 0; i < 32; i++)
      mem_write(i, 8'h00);

    // Program sequence:
    //   00: LDA 1C   → Acc ← 5
    //   01: STO 1A   → mem_wr MUST assert here
    //   02: HLT
    mem_write(8'h00, 8'b101_11100);  // LDA 1C
    mem_write(8'h01, 8'b110_11010);  // STO 1A
    mem_write(8'h02, 8'b000_00000);  // HLT

    // Data
    mem_write(8'h1C, 8'h05);         // Value to load into accumulator
    mem_write(8'h1A, 8'h00);         // Store destination
  endtask


// =============================================================
// TEST 5–8 (functional variations)
// =============================================================
  task automatic load_test5();
    int i;
    for (i = 0; i < 32; i++) mem_write(i, 8'h00);

    mem_write(8'h00, 8'b111_00011);
    mem_write(8'h01, 8'h00);
    mem_write(8'h02, 8'h00);
    mem_write(8'h03, 8'b101_11010);
    mem_write(8'h04, 8'b110_11100);
    mem_write(8'h05, 8'b111_00011);

    mem_write(8'h1A, 8'h0A);
    mem_write(8'h1C, 8'h00);
  endtask

  task automatic load_test6();
    int i;
    for (i = 0; i < 32; i++) mem_write(i, 8'h00);

    // SKZ zero=0 then SKZ zero=1
    mem_write(8'h00, 8'b101_11010);
    mem_write(8'h01, 8'b100_11101);
    mem_write(8'h02, 8'b001_00000);

    mem_write(8'h03, 8'b101_11100);
    mem_write(8'h04, 8'b100_11101);
    mem_write(8'h05, 8'b001_00000);

    mem_write(8'h07, 8'b111_00000);

    mem_write(8'h1A, 8'hAA);
    mem_write(8'h1C, 8'h00);
    mem_write(8'h1D, 8'h00);
  endtask

  task automatic load_test7();
    int i;
    for (i = 0; i < 32; i++) mem_write(i, 8'h00);

    // Test jump inside ALU stage
    mem_write(8'h00, 8'b111_00011);
    mem_write(8'h01, 8'h00);
    mem_write(8'h02, 8'h03);

    mem_write(8'h03, 8'b101_11010);
    mem_write(8'h1A, 8'h05);
  endtask

  task automatic load_test8();
    int i;
    for (i = 0; i < 32; i++) mem_write(i, 8'h00);

    // Force zero = 1 for SKZ
    mem_write(8'h00, 8'b101_11100);
    mem_write(8'h01, 8'b001_00000);
    mem_write(8'h02, 8'b111_00000);

    mem_write(8'h1C, 8'h00);
  endtask


// =============================================================
// TEST 9 — Random Program Generator
// =============================================================
  task automatic load_test9();
    int i, t;
    for (i = 0; i < 32; i++) mem_write(i, 8'h00);

    for (t = 0; t < 25; t++) begin
      byte opc;
      int randAddr = $urandom_range(0,31);
      case ($urandom_range(0,7))
        0: opc = {ADD, randAddr};
        1: opc = {AND, randAddr};
        2: opc = {XOR, randAddr};
        3: opc = {LDA, randAddr};
        4: opc = {STO, randAddr};
        5: opc = {SKZ, randAddr};
        6: opc = {JMP, randAddr};
        7: opc = {HLT, 5'h00};
      endcase
      mem_write(t, opc);
    end

    // Always end program with a HLT
    mem_write(25, {HLT, 5'h00});

    // Fill remaining memory with random data
    for (i = 26; i < 32; i++)
      dut.mem1.memory[i] = $urandom_range(0,255);
  endtask


// =============================================================
// MAIN TEST EXECUTION + PC CHECKING + cover()
// =============================================================
  initial begin
    int pc;
    bit pass1, pass2, pass3;

    $display("========= CPU FULL TEST SUITE =========");
    $display("[INFO] TEST_SELECTION = %0d", TEST_SELECTION);

    // --------------------------------------
    // TEST 1
    // --------------------------------------
    if (TEST_SELECTION == TEST_ALL || TEST_SELECTION == TEST_1) begin
      do_reset(); load_test1(); run_until_halt(3000, pc);
      pass1 = (pc == 8'h17);
      $display("Test1 Result: %s (PC=%0d)", pass1 ? "PASS" : "FAIL", pc);
      cover (pc == 8'h17);
    end

    // --------------------------------------
    // TEST 2
    // --------------------------------------
    if (TEST_SELECTION == TEST_ALL || TEST_SELECTION == TEST_2) begin
      do_reset(); load_test2(); run_until_halt(3000, pc);
      pass2 = (pc == 8'h10);
      $display("Test2 Result: %s (PC=%0d)", pass2 ? "PASS" : "FAIL", pc);
      cover (pc == 8'h10);
    end

    // --------------------------------------
    // TEST 3
    // --------------------------------------
    if (TEST_SELECTION == TEST_ALL || TEST_SELECTION == TEST_3) begin
      do_reset(); load_test3(); run_until_halt(8000, pc);
      pass3 = (pc == 8'h0C);
      $display("Test3 Result: %s (PC=%0d)", pass3 ? "PASS" : "FAIL", pc);
      cover (pc == 8'h0C);
    end

    // --------------------------------------
    // TEST 4 — Guaranteed mem_wr activity
    // --------------------------------------
    if (TEST_SELECTION == TEST_ALL || TEST_SELECTION == TEST_4) begin
      do_reset(); load_test4(); run_until_halt(2000, pc);
      $display("Test4_memwr Finished (PC=%0d)", pc);
    end

    // --------------------------------------
    if (TEST_SELECTION == TEST_ALL || TEST_SELECTION == TEST_5) begin
      do_reset(); load_test5(); run_until_halt(2000, pc);
      $display("Test5 Finished (PC=%0d)", pc);
    end

    if (TEST_SELECTION == TEST_ALL || TEST_SELECTION == TEST_6) begin
      do_reset(); load_test6(); run_until_halt(2000, pc);
      $display("Test6 Finished (PC=%0d)", pc);
    end

    if (TEST_SELECTION == TEST_ALL || TEST_SELECTION == TEST_7) begin
      do_reset(); load_test7(); run_until_halt(2000, pc);
      $display("Test7 Finished (PC=%0d)", pc);
    end

    if (TEST_SELECTION == TEST_ALL || TEST_SELECTION == TEST_8) begin
      do_reset(); load_test8(); run_until_halt(2000, pc);
      $display("Test8 Finished (PC=%0d)", pc);
    end


    // =============================================================
    // TEST 9 — RANDOMIZED PROGRAM TESTING
    // =============================================================
    if (TEST_SELECTION == TEST_ALL || TEST_SELECTION == TEST_9) begin
      $display("======== Test9 Random Testing START (Total=%0d) ========",
               RANDOM_TEST_COUNT);

      for (int iter = 0; iter < RANDOM_TEST_COUNT; iter++) begin
        do_reset();
        load_test9();
        run_until_halt(5000, pc);
      end

      $display("======== Test9 Random Testing DONE ========");
    end

    $stop;
  end

endmodule


// =============================================================
// BIND CPU Assertions
// =============================================================
bind cpu cpu_assertions ASSERT_INST();
