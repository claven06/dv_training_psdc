`include "bus_ctrl_if.sv"
`include "bus_ctrl.sv"

module bus_tb;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // $time is a built-in system function
  initial $display(">>>>>>>> SIM TIME START: %0t", $time);
  final   $display(">>>>>>>> SIM TIME END  : %0t", $time);

  // Include all required files
  `include "bus_tran.sv"
  `include "bus_drv.sv"
  `include "bus_seq.sv"
  `include "bus_seq_prio.sv"
  `include "bus_mon.sv"
  `include "bus_sqr.sv"
  `include "bus_agt.sv"
  `include "bus_scb.sv"
  `include "bus_con.sv"
  `include "bus_cov.sv"
  `include "bus_env.sv"
  `include "bus_test.sv"

  bus_ctrl_if bus_if();

  bus_ctrl dut(
    .clk(bus_if.clk_tb),
    .reset_n(bus_if.reset_n_tb),
    .valid(bus_if.valid_tb),
    .write(bus_if.write_tb),
    .addr(bus_if.addr_tb),
    .wdata(bus_if.wdata_tb),
    .rdata(bus_if.rdata),
    .ready(bus_if.ready)
  );

  initial begin
    bus_if.clk_tb = 0;
    forever #5 bus_if.clk_tb = ~bus_if.clk_tb;
  end

  initial begin
    uvm_config_db#(virtual bus_ctrl_if)::set(null, "*", "vif", bus_if);
    uvm_config_db#(virtual bus_ctrl_if)::set(null, "*drv*", "vif", bus_if);
    uvm_config_db#(virtual bus_ctrl_if)::set(null, "*mon*", "vif", bus_if);
    run_test("bus_test");
  end

  initial begin
    $fsdbDumpfile("bus_sim.fsdb");
    $fsdbDumpSVA(0, bus_tb);
    $fsdbDumpvars(0, bus_tb);
  end
endmodule

