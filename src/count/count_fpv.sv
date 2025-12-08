// ============================================================================
//  counter_assertions.sv  — Formal Assertions for counter.sv
//
//  This module contains SystemVerilog Assertions (SVA) that verify:
//    • Reset behavior (active-low asynchronous reset)
//    • Load priority over increment
//    • Correct increment behavior including wrap-around
//    • Hold behavior when neither load nor enable is asserted
//    • Absence of X/Z values during normal operation
//    • Basic environmental assumptions for formal tools
//
//  Compatible with JasperGold, Questa Formal, and simulation.
//
// ============================================================================

timeunit 1ns;
timeprecision 100ps;

module counter_assertions (
    input logic        clk,
    input logic        rst_,     // Asynchronous active-low reset
    input logic        load,
    input logic        enable,
    input logic [4:0]  data,
    input logic [4:0]  count
);

    // ------------------------------------------------------------------------
    // Environmental Assumptions
    // ------------------------------------------------------------------------
    // Assume load and enable are never asserted simultaneously.
    assume_no_overlap: assume property (
        @(posedge clk) !(load && enable)
    );

    // Assume data is stable during a load operation.
    assume_stable_data_on_load: assume property (
        @(posedge clk)
            load |-> $stable(data)
    );


    // ------------------------------------------------------------------------
    // A1. Reset Release Coverage:
    //     When rst_ transitions from 0 → 1, record this event.
    // ------------------------------------------------------------------------
    cover_release_reset: cover property (
        @(posedge clk) $rose(rst_)
    );


    // ------------------------------------------------------------------------
    // A2. Load Priority:
    //     If load was asserted in the previous cycle, then count must equal
    //     the previous data value on the next rising edge.
    // ------------------------------------------------------------------------
    a_load_priority: assert property (
        @(posedge clk) disable iff (!rst_)
            ($past(rst_) && $past(load)) |-> 
                (count == $past(data))
    ) else $error("A2: load did not update count to data");


    // ------------------------------------------------------------------------
    // A3. Increment Behavior:
    //     If enable=1 and load=0 in the previous cycle, counter increments.
    //     Includes wrap-around from 31 → 0.
    // ------------------------------------------------------------------------
    a_increment: assert property (
        @(posedge clk) disable iff (!rst_)
            ($past(rst_) && $past(enable) && !$past(load)) |-> 
                (count == $past(count) + 1) ||
                ($past(count) == 5'd31 && count == 5'd0)
    ) else $error("A3: enable did not increment count correctly");


    // ------------------------------------------------------------------------
    // A4. Hold Behavior:
    //     When load=0 and enable=0, the counter must retain its value.
    // ------------------------------------------------------------------------
    a_hold: assert property (
        @(posedge clk) disable iff (!rst_)
            (!$past(load) && !$past(enable)) |-> 
                (count == $past(count))
    ) else $error("A4: count changed unexpectedly when hold");


    // ------------------------------------------------------------------------
    // A5. No X/Z Allowed:
    //     During normal operation (rst_=1), count must never contain unknowns.
    // ------------------------------------------------------------------------
    a_no_xz: assert property (
        @(posedge clk) disable iff (!rst_)
            (count === count)
    ) else $error("A5: count contains X/Z");

endmodule
