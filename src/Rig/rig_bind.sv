// ------------------------------------------------------------
// bind.sv
// Bind the assertions into the register module
// ------------------------------------------------------------

bind register register_assertions reg_asrt (
    .clk   (clk),
    .rst_  (rst_),
    .enable(enable),
    .data  (data),
    .out   (out)
);

