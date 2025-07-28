
//Assertion Sequence $rose, $fell, $stable
//
//A sequence is a simple building block in System Verilog assertions that can 
//represent certain expressions to aid in creating more complex properties.
//
module tb;
  	bit a;
  	bit clk;

    ///////////////////////////////////////////////////////////////////
	// This sequence states that a should be high on every posedge clk
  	sequence s_a;
      @(posedge clk) a;
    endsequence

  	// When the above sequence is asserted, the assertion fails if 'a'
  	// is found to be not high on any posedge clk
  	assert_a:assert property(s_a);

    ///////////////////////////////////////////////////////////////////
	// This sequence states that 'a' should rise on every posedge clk
  	sequence s_rose_a;
      @(posedge clk) $rose(a);
    endsequence

  	// When the above sequence is asserted, the assertion fails if
  	// posedge 'a' is not found on every posedge clk
  	rose_a:assert property(s_rose_a);

    ///////////////////////////////////////////////////////////////////
	// This sequence states that 'a' should fall on every posedge clk
  	sequence s_fell_a;
      @(posedge clk) $fell(a);
    endsequence

  	// When the above sequence is asserted, the assertion fails if
  	// negedge 'a' is not found on every posedge clk
  	fell_a:assert property(s_fell_a);

    ///////////////////////////////////////////////////////////////////
	// This sequence states that 'a' should be stable on every clock
	// and should not have posedge/negedge at any posedge clk
  	sequence s_stable_a;
      @(posedge clk) $stable(a);
    endsequence

  	// When the above sequence is asserted, the assertion fails if
  	// 'a' toggles at any posedge clk
  	stable_a:assert property(s_stable_a);

    ///////////////////////////////////////////////////////////////////

	always #10 clk = ~clk;

	initial begin
      for (int i = 0; i < 10; i++) begin
        a = $random;
        @(posedge clk);

        // Assertion is evaluated in the preponed region and
        // use $display to see the value of 'a' in that region
        $display("[%0t] a=%0d", $time, a);
      end
      #20 $finish;
    end
endmodule
