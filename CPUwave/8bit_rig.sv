//==============================================================
//  register.sv — 8-bit Register with Enable and Active-Low Reset
//
//  Behavior:
//    • Asynchronous active-low reset clears the register to 0
//    • On each positive clock edge:
//         – If enable = 1 → load new data
//         – Otherwise     → hold previous value
//
//  Ports:
//    clk    — positive-edge clock
//    rst_   — asynchronous active-low reset
//    enable — write-enable control
//    data   — 8-bit input to be stored
//    out    — current stored 8-bit value
//==============================================================

timeunit 1ns;
timeprecision 100ps;

module register
(
    input  logic        clk,      // Clock (posedge-triggered)
    input  logic        rst_,     // Asynchronous active-low reset
    input  logic        enable,   // Load-enable signal
    input  logic [7:0]  data,     // Data input
    output logic [7:0]  out       // Register output
);

    // ------------------------------------------------------------
    // Sequential logic:
    //   – Reset clears register immediately (active-low)
    //   – Otherwise, update on posedge clk if enable is asserted
    // ------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_) begin
        if (!rst_) begin
            // Reset condition: clear register to zero
            out <= 8'b0;
        end
        else if (enable) begin
            // Load new data when enable is high
            out <= data;
        end
        else begin
            // Hold previous value (self-assignment included for clarity)
            out <= out;
        end
    end

endmodule
