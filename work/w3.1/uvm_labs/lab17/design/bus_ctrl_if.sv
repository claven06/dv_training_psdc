interface bus_ctrl_if;
  logic clk_tb;
  logic reset_n_tb;
  logic valid_tb;
  logic write_tb;
  logic [7:0] addr_tb;
  logic [31:0] wdata_tb;
  logic [31:0] rdata;
  logic ready;

  clocking drv_cb @(posedge clk_tb);
    default input #1step output #1;
    output reset_n_tb, valid_tb , write_tb, addr_tb, wdata_tb;
    input rdata, ready;
    endclocking

  clocking mon_cb @(posedge clk_tb);
    default input #1step;
    input reset_n_tb, valid_tb , write_tb, addr_tb, wdata_tb, rdata, ready;
  endclocking

  // Synchronous signal assertion checks
  // When:
  // The testbench starts a transaction (valid_tb=1)
  // The DUT is busy (ready=0)
  // Then:
  // The DUT must assert ready within 1 to 4 clock cycles
  // If not, the assertion fails (indicating a protocol violation)
  property valid_ready_handshake;
    @(posedge clk_tb)
    (valid_tb && !ready)
    |=> ##[1:4] (ready);
    // Below are for debug purpose
    //(valid_tb && !ready, $display("Transaction started at %t", $time))
    //|=> ##[1:4] (ready, $display("Handshake completed at %t", $time));
  endproperty

  assert property (valid_ready_handshake) else
    $error("Valid-Ready handshake violation: Ready didn't arrive within 1-4 cycles after Valid");
endinterface

