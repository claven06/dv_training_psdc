//
//The $value$plusargs system function also searches the list of plusargs like 
//$test$plusargs, but it has the capability to get a value for a specified user
//string. If the prefix of one of the supplied plusargs matches all characters 
//in the given user string, the function will return a non-zero value and store 
//the resulting value in the variable provided. If the user string is not found, 
//then the function returns a non-zero value and the variable will not be 
//modified.
//The user_string shall be of the form "plusarg_string format_string" where 
//format strings are the same as $display tasks. These format identifiers are 
//used to convert the value provided via command line to the given format and 
//store in a variable.
//
// Note FS : Format Specifier

module tb;
  initial begin
  	string  	var1, var2;
    bit [31:0] 	data;

    if ($value$plusargs ("STRING=%s", var1))
      $display ("STRING with FS has a value %s", var1);

    if ($value$plusargs ("NUMBER=%0d", data))
      $display ("NUMBER with %%0d has a value %0d", data);

    if ($value$plusargs ("NUMBER=%0h", data))
      $display ("NUMBER with %%0h has a value %0d", data);

    if ($value$plusargs ("NUMBER=%s", data))
      $display ("NUMBER with %%s has a value %0d", data);

    if ($value$plusargs ("STRING=", var1))
      $display ("STRING without FS has a value %s", var1);

    if ($value$plusargs ("+STRING=%s", var1))
      $display ("STRING with + char has a value %s", var1);

`ifdef RUNTIME_ERR
    if ($value$plusargs ("STRING=%0d", var2))
      $display ("STRING with %%0d has a value %s", var2);
`endif
  end
endmodule
