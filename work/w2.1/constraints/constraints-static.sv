//
//A static constraint is shared across all the class instances.
//Constraints are affected by the static keyword only if they are turned on 
//and off using constraint_mode() method.
//
//When a non-static constraint is turned off using this method, the constraint 
//is turned off in that particular instance of the class which calls the method. 
//But, when a static constraint is turned off and on using this method, the 
//constraint is turned off and on in all the instances of the class.
//
//A constraint block can be declared as static by including the static keyword 
//in its definition.
//
class ABC;
  rand bit [3:0]  a;

  // "c1" is non-static, but "c2" is static
  constraint abc_c1 { a > 5; }
  static constraint abc_c2 { a < 12; }
endclass

class DEF;
  rand bit [3:0]  a;

  // "c1" is non-static, but "c2" is static
  constraint def_c1 { a > 5; }
  static constraint def_c2 { a < 12; }
endclass

module tb;
  initial begin
    ABC abc_obj1 = new;
    ABC abc_obj2 = new;
    DEF def_obj1 = new;
    DEF def_obj2 = new;

    // Turn-off non-static constraint
    abc_obj1.abc_c1.constraint_mode(0);
    // Turn-off static constraint
    def_obj1.def_c2.constraint_mode(0);

    for (int i = 0; i < 5; i++) begin
      abc_obj1.randomize();
      abc_obj2.randomize();
      def_obj1.randomize();
      def_obj2.randomize();
      $display ("abc_obj1.a = %0d, abc_obj2.a = %0d, \
                def_obj1.a = %0d, def_obj2.a = %0d",
                abc_obj1.a, abc_obj2.a, def_obj1.a, def_obj2.a);
    end
  end
endmodule
