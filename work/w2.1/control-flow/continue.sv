module tb;
  	initial begin

      // This for loop increments i from 0 to 9 and exit
      for (int i = 0 ; i < 10; i++) begin

        // Let's create a condition such that the
        // for loop
        if (i == 7)
          continue;

        $display ("Iteration [%0d]", i);
      end
    end
endmodule
