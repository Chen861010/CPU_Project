// Code your design here
// register.sv
timeunit 1ns; 
timeprecision 100ps;

module register
(
    input  logic        clk,
    input  logic        rst_,   // 題目寫 rst_ (active-low)，我改成 rst_n 比較常見
    input  logic        enable,
    input  logic [7:0]  data,
    output logic [7:0]  out
);

    // 非同步、低有效 reset；上升沿時鐘
    always_ff @(posedge clk or negedge rst_) begin
        if (!rst_)
            out <= 1'b0;
        else if (enable)
            out <= data;
        else
            out <= out; // 保持
    end

endmodule