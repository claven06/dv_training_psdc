
//System Verilog Assertion with time delay
//
//If a is not high on any given clock cycle, the sequence starts and fails on 
//the same cycle. However, if a is high on any clock cycle, the assertion 
//starts and succeeds if b is high 2 clocks cycle later. It fails if b is 
//low 2 clocks cycle later.
//
module tb;
  bit a, b;
  bit clk;
  int i;

  // This is a sequence that says 'b' should be high 2 clocks cycle after
  // 'a' is found high. The sequence is checked on every positive
  // edge of the clock which ultimately ends up having multiple
  // assertions running in parallel since they all span for more
  // than a single clock cycle.
  sequence s_ab;
    @(posedge clk) a ##2 b;
  endsequence

  // Print a display statement if the assertion passed
  assert property(s_ab)
  	$display ("[%0t] Assertion passed !", $time);

  always #10 clk = ~clk;

  initial begin
    for (i = 0; i < 10; i++) begin
      @(posedge clk);
      a <= $random;
      b <= $random;

      $display("[T=%0t][i=%0d] a=%b b=%b", $time,i,a, b);
    end

    #20 $finish;
  end
endmodule
