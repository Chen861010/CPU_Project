  timeunit        1ns ;
  timeprecision 100ps ;
module scale_mux #(parameter int WIDTH = 8) (
  input  logic [WIDTH-1:0] in_a,   // Input A
  input  logic [WIDTH-1:0] in_b,   // Input B
  input  logic             sel_a,  // Select signal: 1 -> in_a, 0 -> in_b
  output logic [WIDTH-1:0] out     // Output
);
  always_comb begin
    out = sel_a ? in_a : in_b;
  end
endmodule
