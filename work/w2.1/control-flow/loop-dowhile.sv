module tb;
 bit clk;

  always #10 clk = ~clk;

  initial begin
  	bit [3:0] counter;

    $display ("Counter = %0d", counter);      // Counter = 0
		do begin
			@ (posedge clk);
			counter ++;
          $display ("Counter = %0d", counter);      // Counter increments
        end while (counter < 5);
    $display ("Counter = %0d", counter);      // Counter = 5 
    $finish;
  end

  endmodule
