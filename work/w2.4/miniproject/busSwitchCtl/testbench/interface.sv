// Switch interface contains all signals that the switch requires
// to operate
interface switch_if #(
     parameter int ADDR_WIDTH,
     parameter int DATA_WIDTH
) ();
    logic                     rstn;
    logic                     vld;
    logic [ADDR_WIDTH-1:0]    addr;
    logic [DATA_WIDTH-1:0]    data;
    logic [ADDR_WIDTH-1:0]    addr_a;
    logic [DATA_WIDTH-1:0]    data_a;
    logic [ADDR_WIDTH-1:0]    addr_b;
    logic [DATA_WIDTH-1:0]    data_b;
endinterface

// Although an adder does not have a clock, let us create a mock clock
// used in the testbench to synchronize when value is driven and when
// value is sampled. Typically combinational logic is used between
// sequential elements like FF in a real circuit. So, let us assume
// that inputs to the adder is provided at some posedge clock. But because
// the design does not have clock in its input, we will keep this clock
// in a separate interface that is available only to testbench components
interface clk_if();
  logic tb_clk;

  initial tb_clk <= 0;

  always #10 tb_clk = ~tb_clk;
endinterface
