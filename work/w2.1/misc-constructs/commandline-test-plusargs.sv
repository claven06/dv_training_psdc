//
//Every now and then you come across the need to avoid testbench recompilation, 
//and instead be able to accept values from the command line just like any 
//scripting language like bash or perl would do. In System Verilog, this 
//information is provided to the simulation as an optional argument always 
//starting with the + character. These arguments passed in from the command line 
//are accessible in SV code via the following system functions called as plusargs.
//Syntax
//  $test$plusargs (user_string)
//  $value$plusargs (user_string, variable)
//
//$test$plusargs
//The function $test$plusargs is typically used when a value for the argument 
//is not required. It searches the list of plusargs for a user specified string. 
//A variable can also be used to specify the string, and any null character 
//will be ignored. If the prefix of one of the supplied plusargs matches all 
//characters in the provided string, the function will return a non-zero 
//integer, and otherwise zero.
//
module tb;
  initial begin
    if ($test$plusargs ("STANDBY"))
      $display ("STANDBY argument is found ...");

    if ($test$plusargs ("Standby"))
      $display ("Standby argument is also found ...");

    if ($test$plusargs ("STAND"))
      $display ("STAND substring is found ...");

    if ($test$plusargs ("S"))
      $display ("Some string starting with S found ...");

    if ($test$plusargs ("T"))
      $display ("Some string containing T found ...");

    if ($test$plusargs ("STAND_AT_EASE"))
      $display ("Can't stand any longer ...");

    if ($test$plusargs ("SUNSHADE"))
      $display ("It's too hot today ...");

    if ($test$plusargs ("WINTER"))
      $display ("No match.. ");
  end
endmodule
