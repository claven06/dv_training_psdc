`include "top_uvm_pkg.sv"

module top_tb;
  import uvm_pkg::*;
  import top_uvm_pkg::*;

  initial begin
    run_test("top_first_test");
  end

endmodule
