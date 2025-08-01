// Adder interface contains all signals that the adder requires
// to operate
interface adder_if();
  logic 		rstn;
  logic [7:0] 	a;
  logic [7:0] 	b;
  logic [7:0] 	sum;
  logic 		carry;
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
