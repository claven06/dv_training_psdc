interface myBus #(parameter D_WIDTH=8) (input clk);
  logic [D_WIDTH-1:0]  data;
  logic                enable;

  // From TestBench perspective, 'data' is input and 'write' is output
  modport TB  (input data, clk, output enable);

  // From DUT perspective, 'data' is output and 'enable' is input
  modport DUT (output data, input enable, clk);

endinterface

module dut (myBus busIf);
  always @ (posedge busIf.clk)
    if (busIf.enable)
      busIf.data <= busIf.data+1;
    else
      busIf.data <= 0;
endmodule


// Filename : tb_top.sv
module tb_top;
  bit clk;

  // Create a clock
  always #10 clk = ~clk;

  // Create an interface object
  myBus busIf (clk);

  // Instantiate the DUT; pass modport DUT of busIf
  dut dut0 (busIf.DUT);

  // Testbench code : let's wiggle enable
  initial begin
    busIf.enable  <= 0;
    #10 busIf.enable <= 1;
    #40 busIf.enable <= 0;
    #20 busIf.enable <= 1;
    #100 $finish;
  end

  initial begin
    // Monitor signals
    $monitor("T=%0d clk=%b enable=%b data=%b",$time,clk,busIf.enable,busIf.data);
    //enable wave dump
    $dumpfile("dump.vcd"); 
    $dumpvars;
  end
    
endmodule
