//Without solve-before
//When a is 0, b can take any of the 4 values. So there are 4 combinations here. 
//Next when a is 1, b can take only 1 value and so there is only 1 combination 
//possible.
//Hence there are 5 possible combinations and if the constraint solver has to 
//allot each an equal probability, the probability to pick any of the combination is 1/5.
//
class ABC;
  rand  bit			a;
  rand  bit [1:0] 	b;

  //The constraint ensures that b gets 0x3 whenever a is 1. 
  constraint abc_ab { a -> b == 3'h3; }  
endclass

//With solve-before
//System Verilog allows a mechanism to order variables so that a can be chosen 
//independently of b. This is done using solve keyword.
//Here, a is solved first and based on what it gets b is solved next.
//
//Because a is solved first, the probability of choosing either 0 or 1 is 50%. 
//Next, the probability of choosing a value for b depends on the value chosen 
//for a.
//
class DEF; 
  rand  bit			a;
  rand  bit [1:0] 	b;

  constraint def_ab { a -> b == 3'h3;

  				  // Tells the solver that "a" has
  				  // to be solved before attempting "b"
  				  // Hence value of "a" determines value
  				  // of "b" here
                  	solve a before b;
                  }
endclass

module tb;
  initial begin
    ABC abc = new;
    DEF def = new;

    for (int i = 0; i < 8; i++) begin
      abc.randomize();
      def.randomize();
      $display ("abc.a=%0d abc.b=%0d def.a=%0d def.b=%0d", abc.a, abc.b, def.a, def.b);
    end
  end
endmodule
