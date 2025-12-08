module register_test;
timeunit 1ns;
timeprecision 100ps;

logic clk = 0;
logic rst_ = 1;
logic enable;
logic [7:0] data;
logic [7:0] out;

`define PERIOD 10

always #(`PERIOD/2) clk = ~clk;

// DUT
register dut (.clk(clk), .rst_(rst_), .enable(enable), .data(data), .out(out));


// =============================================================
//  Coverage Group (Cadence / Questa OK)
// =============================================================
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

  en_x_data : cross enable, data;
  rst_x_en  : cross rst_,   enable;

endgroup

reg_cg cg_inst = new();


// =============================================================
//  Golden Model (跟 RTL 一樣的行為，包含 async reset)
// =============================================================
logic [7:0] expected;

always_ff @(posedge clk or negedge rst_) begin
  if (!rst_)
    expected <= 8'h00;
  else if (enable)
    expected <= data;
  // enable==0 時，自然保持
end


// =============================================================
// SIMPLE RANDOM TEST + 偶爾出現的 rst_ pulse
// =============================================================
int NUM_RANDOM_TESTS = 10000;
int reset_cooldown   = 0;   // 用來控制 reset 間隔

initial begin
  int i;

  // Initial reset
  rst_   = 0;
  enable = 0;
  data   = 0;

  @(negedge clk);
  rst_ = 1;   // 釋放 reset

  $display("Starting SIMPLE RANDOM TEST ...");

  for (i = 0; i < NUM_RANDOM_TESTS; i++) begin

    //---------------------------------------------------------
    // 1) 在 negedge clk 產生下一拍的輸入 & reset
    //---------------------------------------------------------
    @(negedge clk);

    // ---- 隨機產生 reset_pulse，每隔一段時間才可能出現 ----
    if (reset_cooldown == 0 && $urandom_range(0,99) < 5) begin
      // 約 5% 機率觸發 reset pulse
      rst_          = 0;
      reset_cooldown = $urandom_range(20,50); // 下次 reset 之前至少隔 20~50 個 cycle
    end
    else begin
      rst_ = 1;
      if (reset_cooldown > 0)
        reset_cooldown--;
    end

    // 隨機 enable / data
    enable = $urandom_range(0,1);
    data   = $urandom;

    //---------------------------------------------------------
    // 2) 下一個 posedge clk → DUT & expected 都更新
    //---------------------------------------------------------
    @(posedge clk);

    //---------------------------------------------------------
    // 3) 只在「非 reset 且 enable=1」時檢查
    //---------------------------------------------------------
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
