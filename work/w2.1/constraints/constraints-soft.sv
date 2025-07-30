//
//Soft constraint
//The normal constraints are called hard constraints because it is mandatory 
//for the solver to always satisfy them. If the solver fails to find a solution, 
//then the randomization will fail.
//However, a constraint declared as soft gives the solver some flexibility that 
//the constraint need not to be satisfied if there are other contradicting 
//constraints - either hard or a soft constraint with higher priority.
//Soft constraints are used to specify default value and distributions for 
//random variables.
//
class ABC;
  rand bit [3:0] data;

  // This constraint is defined as "soft"
  constraint c_data {soft data >= 4;
                     data <= 12; }
endclass

module tb;
  ABC abc;

  initial begin
    abc = new;
    for (int i = 0; i < 5; i++) begin
//      abc.randomize();
      abc.randomize() with {data == 2;};
      $display ("abc = 0x%0h", abc.data);
    end
  end
endmodule
