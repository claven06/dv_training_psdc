`timescale 1ns/1ns

module des (input req, clk, output reg gnt);
  always @ (posedge clk)
    if (req)
      gnt <= 1;
  	else
      gnt <= 0;
endmodule

interface _if (input bit clk);
  logic gnt;
  logic req;

  clocking cb_5 @(posedge clk);
    input #5 gnt;
    input #0 output #5  req;
  endclocking

  clocking cb_0 @(posedge clk);
    input #0 gnt;
    input #0 output #0  req;
  endclocking

  clocking cb_2 @(posedge clk);
    input #2 gnt;
    input #0 output #2 req;
  endclocking

  clocking cb_15 @(posedge clk);
    input #15 gnt;
    input #0 output #15  req;
  endclocking

endinterface

module tb;
  bit clk;

  // Create a clock and initialize input signal
  always #10 clk = ~clk;
  initial begin
    clk <= 0;
    if0.cb_0.req <= 0;
    if0.cb_2.req <= 0;
    if0.cb_5.req <= 0;
    if0.cb_15.req <= 0;
  end

  // Instantiate the interface
  _if if0 (.clk (clk));

  // Instantiate the design
  des d0 ( .clk (clk),
           .req (if0.req),
           .gnt (if0.gnt));

  // Drive stimulus
  initial begin
    for (int i = 0; i < 10; i++) begin
      repeat (5) @(posedge if0.clk);

      if0.cb_0.req <= ~if0.cb_0.req;
      if0.cb_2.req <= ~if0.cb_2.req;
      if0.cb_5.req <= ~if0.cb_5.req;
      if0.cb_15.req <= ~if0.cb_15.req;
    end
    #20 $finish;
  end

  initial begin
    // Monitor signals
    $monitor("T=%0t clk=%0b req=%0b gnt=%0b",$time,clk,if0.req,if0.gnt);
    $monitor("T=%0t clk=%0b cb_0.req=%0b  cb_0.gnt=%0b ",$time,clk,if0.cb_0.req,if0.cb_0.gnt);
    $monitor("T=%0t clk=%0b cb_2.req=%0b  cb_2.gnt=%0b ",$time,clk,if0.cb_2.req,if0.cb_2.gnt);
    $monitor("T=%0t clk=%0b cb_5.req=%0b  cb_5.gnt=%0b ",$time,clk,if0.cb_5.req,if0.cb_5.gnt);
    $monitor("T=%0t clk=%0b cb_15.req=%0b cb_15.gnt=%0b",$time,clk,if0.cb_15.req,if0.cb_15.gnt);
    //enable wave dump
    // $vcdplusfile("dump.vpd");  // Set file name
    //$vcdpluson;                // Start dumping all signals
    $fsdbDumpfile("dump.fsdb");       // Specify output file name
    $fsdbDumpvars(0, tb);  // Dump all signals under the testbench
  end

endmodule
