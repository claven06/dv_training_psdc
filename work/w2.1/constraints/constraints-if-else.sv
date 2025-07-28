//
//In the code shown below, the first if block checks whether mode is 
//inside 5 and 11. If this condition is true, then mod_en should be 
//constrained to 1 and if it is false, then the else part is executed. 
//There is another if-else block within the else part which checks 
//if mode is 1 and tries to satisfy the constraints mentioned in 
//the appropriate parts.
//
class ABC;
  rand bit [3:0] mode;
  rand bit 		 mod_en;

  constraint c_mode {
    					// If 5 <= mode <= 11, then constrain mod_en to 1
    					// This part only has 1 statement and hence do not
    					// require curly braces {}
    					if (mode inside {[4'h5:4'hB]})
  							mod_en == 1;

    					// If the above condition is false, then do the following
   						else {
                          // If mode is constrained to be 1, then mod_en should be 1
                          if ( mode == 4'h1) {
      							mod_en == 1;
                            // If mode is any other value than 1 and not within
                            // 5:11, then mod_en should be constrained to 0
    						} else {
      							mod_en == 0;
    						}
  						}
                    }

endclass

module tb;
  initial begin
    ABC abc = new;
    for (int i = 0; i < 10; i++) begin
    	abc.randomize();
      $display ("mode=0x%0h mod_en=0x%0h", abc.mode, abc.mod_en);
    end
  end

endmodule
