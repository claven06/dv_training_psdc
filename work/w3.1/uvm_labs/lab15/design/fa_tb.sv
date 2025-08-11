`include "fadder_if.sv"
`include "fadder.sv"

module fa_tb;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // $time is a built-in system function
  initial $display(">>>>>>>> SIM TIME START: %0t", $time);
  final   $display(">>>>>>>> SIM TIME END  : %0t", $time);

  // Include all required files
  `include "fa_tran.sv"
  `include "fa_drv.sv"
  `include "fa_seq.sv"
  `include "fa_mon.sv"
  `include "fa_sqr.sv"
  `include "fa_agt.sv"
  `include "fa_scb.sv"
  `include "fa_env.sv"
  `include "fa_test.sv"

  fadder_if fa_if();

  fadder dut(
    .a(fa_if.a_tb),
    .b(fa_if.b_tb),
    .cin(fa_if.cin_tb),
    .sum(fa_if.sum),
    .cout(fa_if.cout)
  );

  initial begin
    fa_if.clk_tb = 0;
    forever #5 fa_if.clk_tb = ~fa_if.clk_tb;
  end

  initial begin
    uvm_config_db#(virtual fadder_if)::set(null, "*", "vif", fa_if);
    run_test("fa_test");
  end

  initial begin
    $fsdbDumpfile("fa_sim.fsdb");
    $fsdbDumpSVA(0, fa_tb);
    $fsdbDumpvars(0, fa_tb);
  end
endmodule

