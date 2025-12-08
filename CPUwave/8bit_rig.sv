// register.sv
timeunit 1ns;
timeprecision 100ps;

module register
(
    input  logic        clk,       // Clock signal (positive-edge triggered)
    input  logic        rst_,      // Asynchronous active-low reset
    input  logic        enable,    // Enable signal to update the register
    input  logic [7:0]  data,      // 8-bit input data to be stored
    output logic [7:0]  out        // 8-bit output (stored register value)
);

    // Sequential logic:
    //  - Asynchronous reset (active low)
    //  - Synchronous update on the rising edge of clk
    always_ff @(posedge clk or negedge rst_) begin
        if (!rst_) begin
            // When reset is asserted (low), clear the register to 0
            out <= 8'b0;
        end
        else if (enable) begin
            // When enable is asserted, store the new input data
            out <= data;
        end
        else begin
            // When enable is not asserted, hold the previous value
            // (explicit self-assignment is optional)
            out <= out;
        end
    end

endmodule
