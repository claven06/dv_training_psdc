interface fadder_if;
  logic a_tb;     // Input to DUT (driven by testbench)
  logic b_tb;
  logic cin_tb;
  logic sum;
  logic cout;
  logic clk_tb;

  // Modport for driver
  modport drv_mp (
    output a_tb, b_tb, cin_tb,  // Driver drives DUT inputs
    input  sum, cout,           // Driver reads DUT outputs
    input  clk_tb               // Driver needs clock for timing
  );

  // Modport for monitor
  modport mon_mp (
    input a_tb, b_tb, cin_tb, sum, cout, clk_tb  // Monitor only reads
  );

  clocking drv_cb @(posedge clk_tb);
    output a_tb, b_tb, cin_tb;
    input sum, cout;
  endclocking

  clocking mon_cb @(posedge clk_tb);
    input a_tb, b_tb, cin_tb, sum, cout;
  endclocking

  task automatic init_tb();
    a_tb = 0;
    b_tb = 0;
    cin_tb = 0;
  endtask

endinterface

