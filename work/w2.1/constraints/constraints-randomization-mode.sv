//
//rand_mode
//Randomization of variables in a class can be disabled using rand_mode 
//method call.
//This is very similar to the constraint_mode() method used to Disable 
//Constraints. So a disabled random variable is treated the same as if they had 
//not been declared rand or randc.
//rand_mode can be called both as a function and task. Current state of the 
//variable will be returned if it is called as a function.
//
// Create a class that contains random variables
class Fruits;
  rand bit [3:0] var1;
  rand bit [1:0] var2;
endclass

module tb;
  initial begin
  	// Instantiate an object of the class
    Fruits f = new();

    // Print values of those variables before randomization
    $display ("Before randomization var1=%0d var2=%0d", f.var1, f.var2);

    // Turn off randomization for var1
    //f.var1.rand_mode (0);
    
    // Turns off randomization for all variables
    //f.rand_mode (0);

    // rand_mode() is called as a function which returns the state of the given variable
    // If it is enabled, then print a statement
    if (f.var1.rand_mode())
    	if (f.var2.rand_mode())
      		$display ("Randomization of all variables is enabled");
        else 
            $display ("Randomization of var1 is enabled & var2 is disabled");
    else 
        if (f.var2.rand_mode()) 
            $display ("Randomization of var1 is disabled & var2 is enabled");
        else
            $display ("Randomization of all variables is disabled");

    // Randomize the class object which in turn randomizes all internal variables
    // declared using rand/randc keywords
    f.randomize();

    // Print the value of these variables after randomization
    $display ("After randomization var1=%0d var2=%0d", f.var1, f.var2);
  end
endmodule
