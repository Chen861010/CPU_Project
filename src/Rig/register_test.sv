//==============================================================
//  register_test.sv — Self-Checking Testbench for 8-bit Register
//
//  Features:
//    • Asynchronous active-low reset testing
//    • Randomized enable/data stimulus
//    • Occasional randomized reset pulses
//    • Golden model for cycle-accurate checking
//    • Functional coverage: enable, reset, data, output, crosses
//
//  This testbench validates correct behavior of register.sv.
//==============================================================

module register_test;
timeunit 1ns;
timeprecision 100ps;

// ------------------------------------------------------------
// Clock generation
// ------------------------------------------------------------
logic clk = 0;
logic rst_ = 1;
logic enable;
logic [7:0] data;
logic [7:0] out;

`define PERIOD 10
always #(`PERIOD/2) clk = ~clk;


// ------------------------------------------------------------
// DUT instantiation
// ------------------------------------------------------------
register dut (
    .clk(clk),
    .rst_(rst_),
    .enable(enable),
    .data(data),
    .out(out)
);


//==============================================================
//  Functional Coverage
//==============================================================
covergroup reg_cg @(posedge clk);

  cp_enable : coverpoint enable {
    bins en0 = {0};
    bins en1 = {1};
  }

  cp_rst : coverpoint rst_ {
    bins rst0 = {0};
    bins rst1 = {1};
  }

  cp_data : coverpoint data {
    bins zero   = {8'h00};
    bins ff     = {8'hFF};
    bins others = default;
  }

  cp_out : coverpoint out {
    bins all_vals[] = {[0:255]};
  }

  // Cross coverage: enable × data, reset × enable
  en_x_data : cross enable, data;
  rst_x_en  : cross rst_, enable;

endgroup

reg_cg cg_inst = new();


//==============================================================
//  Golden Model (mirrors RTL behavior exactly)
//==============================================================
logic [7:0] expected;

always_ff @(posedge clk or negedge rst_) begin
    if (!rst_)
        expected <= 8'h00;
    else if (enable)
        expected <= data;
    // When enable=0 → hold previous value implicitly
end


//==============================================================
//  Simple Random Test
//    • Randomized enable/data each cycle
//    • Random asynchronous reset pulses
//    • Checks only when not in reset and enable=1
//==============================================================
int NUM_RANDOM_TESTS = 10000;
int reset_cooldown   = 0;

initial begin
    int i;

    // Initial reset sequence
    rst_   = 0;
    enable = 0;
    data   = 0;

    @(negedge clk);
    rst_ = 1;

    $display("Starting SIMPLE RANDOM TEST ...");

    for (i = 0; i < NUM_RANDOM_TESTS; i++) begin

        //------------------------------------------------------
        // 1) Drive inputs and possible reset pulse on negedge
        //------------------------------------------------------
        @(negedge clk);

        // Random asynchronous reset pulse (5% probability)
        if (reset_cooldown == 0 && $urandom_range(0,99) < 5) begin
            rst_ = 0;
            reset_cooldown = $urandom_range(20,50);
        end else begin
            rst_ = 1;
            if (reset_cooldown > 0)
                reset_cooldown--;
        end

        // Random enable and data
        enable = $urandom_range(0,1);
        data   = $urandom;


        //------------------------------------------------------
        // 2) Evaluate DUT and reference model on posedge
        //------------------------------------------------------
        @(posedge clk);


        //------------------------------------------------------
        // 3) Only check when not in reset and enable=1
        //------------------------------------------------------
        if (rst_ && enable) begin
            if (out !== expected) begin
                $display("FAIL @ time %0t, iter %0d", $time, i);
                $display("  rst_=%0b en=%0b data=%h out=%h expected=%h",
                         rst_, enable, data, out, expected);
                $finish;
            end
        end

    end

    $display("ALL SIMPLE RANDOM TESTS PASSED!");
    $stop;
end


endmodule
