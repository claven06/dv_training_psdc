module tb;
 bit clk;

  always #10 clk = ~clk;
  initial begin
  	bit [3:0] counter;

    $display ("Counter = %0d", counter);      // Counter = 0
  	while (counter < 10) begin
    	@(posedge clk);
    	counter++;
        $display ("Counter = %0d", counter);      // Counter increments
  	end
  	$display ("Counter = %0d", counter);      // Counter = 10
    $finish;
end
endmodule
