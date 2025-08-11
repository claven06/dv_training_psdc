interface fadder_if;
  logic a_tb;     // Input to DUT (driven by testbench)
  logic b_tb;
  logic cin_tb;
  logic sum;
  logic cout;
  logic clk_tb;

  clocking drv_cb @(posedge clk_tb);
    output a_tb, b_tb, cin_tb;
    input sum, cout;
  endclocking

  clocking mon_cb @(posedge clk_tb);
    input a_tb, b_tb, cin_tb, sum, cout;
  endclocking
endinterface

