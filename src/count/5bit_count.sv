//==============================================================
//  counter.sv — 5-bit Up Counter with Load and Active-Low Reset
//
//  Description:
//    • Asynchronous active-low reset clears the counter to 0
//    • On each positive clock edge:
//         – If load = 1 → count is set to input data
//         – Else if enable = 1 → count increments by 1
//         – Otherwise → hold previous value
//
//  Ports:
//    data   — 5-bit load value
//    load   — load-enable signal (higher priority than enable)
//    enable — increment-enable signal
//    clk    — positive-edge clock
//    rst_   — asynchronous active-low reset
//    count  — 5-bit counter output
//==============================================================

timeunit 1ns;
timeprecision 100ps;

module counter (
    input  logic [4:0] data,     // 5-bit input value for load
    input  logic       load,     // Load control (active high)
    input  logic       enable,   // Increment control (active high)
    input  logic       clk,      // Clock (posedge triggered)
    input  logic       rst_,     // Asynchronous active-low reset
    output logic [4:0] count     // 5-bit counter output
);

    // ------------------------------------------------------------
    // Sequential logic:
    //   — Reset has highest priority
    //   — Load overrides increment
    // ------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_) begin
        if (!rst_) begin
            // Reset: force counter to zero
            count <= 5'd0;
        end
        else if (load) begin
            // Load new count value
            count <= data;
        end
        else if (enable) begin
            // Increment counter by 1
            count <= count + 1'b1;
        end
        // else: hold previous value (implicit)
    end

endmodule
