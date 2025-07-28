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
      bit[3:0] delay = $random;
      $display("[T=%0t] i=%0d delay=%0d",$time,i,delay);
      repeat (delay) @(posedge if0.clk);
//      if0.cb_5.req <= ~if0.cb_5.req;

      case(i%3)
      0: if0.cb_0.req <= ~if0.cb_0.req;
      1: if0.cb_2.req <= ~if0.cb_2.req;
      2: if0.cb_5.req <= ~if0.cb_5.req;
      endcase

    end
    #20 $finish;
  end

  initial begin
    // Monitor signals
    $monitor("T=%0t clk=%0b req=%0b gnt=%0b",$time,clk,if0.req,if0.gnt);
    //enable wave dump
    $dumpfile("dump.vcd"); 
    $dumpvars;
  end

endmodule
