module tb;

  initial begin
    int a, res;

    // 1. Lets pick a random value from 1 to 10 and assign to "a"
    a = $urandom_range(1, 10);

    $display ("Before calling fn: a=%0d res=%0d", a, res);

    // Function is called with "pass by value" which is the default mode
    res = fn(a);

    // Even if value of a is changed inside the function, it is not reflected here
    $display ("After calling fn: a=%0d res=%0d", a, res);
  end

  // Use "ref" to make this function accept arguments by reference
  // also make the function automatic. It is illigal to use argument passing
  // by reference for subroutines with a lifetime of static
  function automatic int fn(ref int a);

    // Any change to this local variable will be 
  	// reflected in the main variable declared above within the
  	// initial block
    a = a + 5;

    // Return some computed value
    return a * 10;
  endfunction

endmodule
