module tb;
  bit [1:0] 	abc;

  initial begin
    abc = 1;

    // None of the case items match the value in "abc"
    // A violation is reported here
    unique case (abc)
      0 : $display ("Found to be 0");
      2 : $display ("Found to be 2");
    endcase
  end
endmodule
