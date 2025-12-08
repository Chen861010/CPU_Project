///////////////////////////////////////////////////////////////////////////
// (c) Copyright 2013 Cadence Design Systems, Inc. All Rights Reserved.
//
// File name   : scale_mux_test.sv
// Title       : MUX Testbench Module
// Project     : SystemVerilog Training
// Description : Defines the mux testbench module (Enhanced with coverage
//               and random testing, simplified bins for Cadence/Questa)
///////////////////////////////////////////////////////////////////////////

module scale_mux_test;

  timeunit        1ns;
  timeprecision 100ps;

  localparam WIDTH = 8;

  logic [WIDTH-1:0] out;
  logic [WIDTH-1:0] in_a;
  logic [WIDTH-1:0] in_b;
  logic             sel_a;

  // Instantiate DUT
  scale_mux #(WIDTH) mux8 (.out(out), .in_a(in_a), .in_b(in_b), .sel_a(sel_a));


  // ============================================================
  // Simplified Coverage Groups (No huge bins!)
  // ============================================================

  // Coverage for sel_a only
  covergroup cg_sel @(posedge sel_a);
    coverpoint sel_a { bins a0 = {0}; bins a1 = {1}; }
  endgroup

  // Functional correctness coverage
  covergroup cg_function @(posedge sel_a);
    cp_correct : coverpoint out {
      bins correct_from_a = { in_a } iff (sel_a == 1);
      bins correct_from_b = { in_b } iff (sel_a == 0);
    }
  endgroup

  cg_sel       cov_sel = new();
  cg_function  cov_func = new();


  // ============================================================
  // Monitor
  // ============================================================
  initial begin
     $timeformat(-9, 0, "ns", 3);
     $monitor("%t in_a=%h in_b=%h sel_a=%h out=%h",
               $time, in_a, in_b, sel_a, out);
  end


  // ============================================================
  // Check Function
  // ============================================================
  task xpect(input [WIDTH-1:0] expected);
    if (out !== expected) begin
      $display("ERROR: out=%b expected=%b", out, expected);
      $display("MUX TEST FAILED");
      $finish;
    end
  endtask


  // ============================================================
  // Random Test (user-controlled)
  // ============================================================
  integer rand_iter = 2000;   // ← 你可自行修改次數

  task run_random_test;
    integer i;
    logic [WIDTH-1:0] expected;

    for (i = 0; i < rand_iter; i++) begin
      in_a  = $urandom;
      in_b  = $urandom;
      sel_a = $urandom % 2;

      expected = (sel_a) ? in_a : in_b;

      #1ns;
      xpect(expected);
    end

    $display("RANDOM TEST (%0d iterations) PASSED", rand_iter);
  endtask


  // ============================================================
  // Apply Deterministic + Random Stimulus
  // ============================================================
  initial begin

      // -----------------------------
      // Deterministic test patterns
      // -----------------------------
      in_a='0; in_b='0; sel_a=0; #1ns xpect('0);
      in_a='0; in_b='0; sel_a=1; #1ns xpect('0);

      in_a='0; in_b='1; sel_a=0; #1ns xpect('1);
      in_a='0; in_b='1; sel_a=1; #1ns xpect('0);

      in_a='1; in_b='0; sel_a=0; #1ns xpect('0);
      in_a='1; in_b='0; sel_a=1; #1ns xpect('1);

      in_a='1; in_b='1; sel_a=0; #1ns xpect('1);
      in_a='1; in_b='1; sel_a=1; #1ns xpect('1);

      $display("MUX DETERMINISTIC TEST PASSED");

      // -----------------------------
      // Random test
      // -----------------------------
      run_random_test();

      $display("ALL MUX TESTS PASSED");
      $stop;
  end

endmodule
