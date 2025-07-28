module tb;
	int x = 4;

  	initial begin
      	// Exits if-else block once the first match is found
      	priority if (x == 4)
      		$display ("x is %0d", x);
      else if (x != 5)
      		$display ("x is %0d", x);
  	end
endmodule
