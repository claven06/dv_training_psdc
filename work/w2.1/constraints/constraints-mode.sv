//
//constraint_mode
//All constraints are by default enabled and will be considered by the 
//System Verilog constraint solver during randomization. A disabled constraint 
//is not considered during randomization.
//Constraints can be enabled or disabled by constraint_mode().
//
//constraint_mode() can be called both as a task and as a function.
//When called as a task, the method does not return anything. The task is 
//supplied with an input argument to either turn on or off the given constraint. 
//When called as a function, the method returns the current state of the given 
//constraint.
//
//
class Fruits;
  rand bit[3:0]  num; 				// Declare a 4-bit variable that can be randomized

  constraint c_num { num > 4;  		// Constraint is by default enabled, and applied
                    num < 9; }; 	// during randomization giving num a value between 4 and 9
endclass

module tb;
  initial begin
    Fruits f = new ();

	// 1. Print value of num before randomization
    $display ("Before randomization num = %0d", f.num);

    // Disable constraint
    f.c_num.constraint_mode(0);

    // 2. Call "constraint_mode" as a function, the return type gives status of constraint
    if (f.c_num.constraint_mode ())
      $display ("Constraint c_num is enabled");
    else
      $display ("Constraint c_num is disabled");

    // 3. Randomize the class object
    f.randomize ();

    // 4. Display value of num after randomization
    $display ("After randomization num = %0d", f.num);
  end
endmodule
