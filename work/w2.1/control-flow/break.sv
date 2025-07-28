module tb;
  	initial begin

      // This for loop increments i from 0 to 9 and exit
      for (int i = 0 ; i < 10; i++) begin
        $display ("Iteration [%0d]", i);

        // Let's create a condition such that the
        // for loop exits when i becomes 7
        if (i == 7)
          break;
      end
    end
endmodule
