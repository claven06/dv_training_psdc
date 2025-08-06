`include "uvm_macros.svh"

module ptop_tb;

  import uvm_pkg::*;
  import ptop_uvm_pkg::*;  // Single import for everything

  initial begin
    `uvm_info("PTOP/TB", "Starting testbench", UVM_LOW)
    run_test("ptop_test");
    `uvm_info("PTOP/TB", "Testbench complete", UVM_LOW)
  end

endmodule
