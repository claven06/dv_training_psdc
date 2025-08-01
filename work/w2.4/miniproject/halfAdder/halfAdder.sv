module halfAdder (input wire a, b, output wire sum, carry);
  
  assign {carry, sum} = a + b;
  
endmodule 
