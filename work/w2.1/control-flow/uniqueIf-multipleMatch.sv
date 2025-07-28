module tb;
	int x = 4;

  	initial begin

      	// This if else if construct is declared to be "unique"
		// When multiple if blocks match, then error is reported
      	unique if (x == 4)
          $display ("1. x is %0d", x);
      	else if (x == 4)
          $display ("2. x is %0d", x);
      	else
          $display ("x is not 4");
  	end
endmodule
