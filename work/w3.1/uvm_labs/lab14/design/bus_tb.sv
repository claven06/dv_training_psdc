module bus_tb;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // $time is a built-in system function
  initial $display(">>>>>>>> SIM TIME START: %0t", $time);
  final   $display(">>>>>>>> SIM TIME END  : %0t", $time);

  // Include all required files
  `include "bus_tran.sv"
  `include "bus_seq.sv"
  `include "bus_seq_prio.sv"
  `include "bus_sqr.sv"
  `include "bus_drv.sv"
  `include "bus_mon.sv"
  `include "bus_agt.sv"
  `include "bus_con.sv"
  `include "bus_scb.sv"
  `include "bus_cov.sv"
  `include "bus_env.sv"
  `include "bus_test.sv"

  initial begin
    run_test("bus_test");
  end

  initial begin
    $fsdbDumpfile("bus_sim.fsdb");
    $fsdbDumpvars(0, bus_tb);
  end
endmodule
