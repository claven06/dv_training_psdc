`include "uvm_macros.svh"

module bus_tb;
   initial $display(">>>>>>>> SIM TIME START: %0t", $time);
   final   $display(">>>>>>>> SIM TIME END  : %0t", $time);

   // Include all required files
   `include "bus_transaction.sv"
   `include "bus_sequence.sv"
   `include "bus_sequencer.sv"
   `include "bus_driver.sv"
   `include "bus_test.sv"

   initial begin
      run_test("bus_test");
   end
endmodule
