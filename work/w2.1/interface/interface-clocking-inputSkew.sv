module des (output reg[3:0] gnt);
  initial gnt <=0;
  always #1 gnt <= $random;
endmodule

interface _if (input bit clk);
  logic [3:0] gnt;

  clocking cb_0 @(posedge clk);
    input #0  gnt;
  endclocking

  clocking cb_1 @(posedge clk);
    input #1step gnt;
  endclocking

  clocking cb_2 @(posedge clk);
    input #1 gnt;
  endclocking

  clocking cb_3 @(posedge clk);
    input #2 gnt;
  endclocking
endinterface

module tb;
  bit clk;

  always #5 clk = ~clk;
  initial   clk <= 0;

  _if if0 (.clk (clk));
  des d0  (.gnt (if0.gnt));

  initial begin
    fork
      begin
        @(if0.cb_0);
        $display ("cb_0.gnt = 0x%0h", if0.cb_0.gnt);
      end
      begin
        @(if0.cb_1);
        $display ("cb_1.gnt = 0x%0h", if0.cb_1.gnt);
      end
      begin
        @(if0.cb_2);
        $display ("cb_2.gnt = 0x%0h", if0.cb_2.gnt);
      end
      begin
        @(if0.cb_3);
        $display ("cb_3.gnt = 0x%0h", if0.cb_3.gnt);
      end
    join
    #10 $finish;
  end

/*  initial begin
    $monitor("[T%0d] clk=%0d, req=%0d, gnt=%0d\n",$time, clk, if0.req, if0.gnt);
    // Dump waves
    $dumpfile("dump.vcd");
    $dumpvars;
  end  
*/

endmodule
