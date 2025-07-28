
//Concurrent assertion
//Two signals a and b are declared and driven at positive edges of a clock 
//with some random value to illustrate how a concurrent assertion works. The 
//assertion is written by the assert statement on an immediate property which 
//defines a relation between the signals at a clocking event.
//
//In this example, both signals a and b are expected to be high at the positive 
//edge of clock for the entire simulation. The assertion is expected to fail 
//for all instances where either a or b is found to be zero.
//
module tb;
    bit a, b;
    bit clk;

    always #10 clk = ~clk;

    initial begin
        for (int i = 0; i < 10; i++) begin
            @(posedge clk);
            a <= $random;
            b <= $random;
            $display("[%0t] a=%0b b=%0b", $time, a, b);
        end
        #10 $finish;
    end

  // This assertion runs for entire duration of simulation
  // Ensure that both signals are high at posedge clk
  // The assertion is expected to fail for all instances 
  // where either a or b is found to be zero.
  assert_AND:assert property (@(posedge clk) a & b);

  // This assertion runs for entire duration of simulation
  // Ensure that atleast 1 of the two signals is high on every clk
  assert_OR:assert property (@(posedge clk) a | b);

  // This assertion runs for entire duration of simulation
  // Ensure that atleast 1 of the two signals is high on every clk
  assert_XNOR:assert property (@(posedge clk) !(!a ^ b));

endmodule
