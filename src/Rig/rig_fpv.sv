module register_assertions(
    input logic clk,
    input logic rst_,
    input logic enable,
    input logic [7:0] data,
    input logic [7:0] out
);

    // 1) 非同步 reset：一拉低就清 0
    property p_async_reset;
        @(negedge rst_) out == 8'h00;
    endproperty
    a_async_reset : assert property (p_async_reset);

    // 2) enable=1 → 下一拍 out 等於這一拍 data
    property p_enable_update;
        @(posedge clk) disable iff (!rst_)
            enable |=> out == $past(data);
    endproperty
    a_enable_update : assert property (p_enable_update);

    // 3) enable=0 → 下一拍 out 保持上一拍的 out
    property p_hold_value;
        @(posedge clk) disable iff (!rst_)
            !enable |=> out == $past(out);
    endproperty
    a_hold_value : assert property (p_hold_value);
    // 4) 
    property p_enable_rst__update;
        @(posedge clk)
           rst_ && enable |=> out == $past(data);
    endproperty
    a_enable_rst__update : assert property(p_enable_rst__update);
endmodule
