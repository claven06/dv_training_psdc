// "T" is a parameter that is set to have a default value of "int"
// Hence "items" will be "int" by default
class stack #(type T = int);
  T item;

  function T add_a (T a);
    return item + a;
  endfunction
endclass

module tb;
	stack 			 	st; 	// st.item is by default of int type
	stack #(bit[3:0]) 	bs; 	// bs.item will become a 4-bit vector
	stack #(real) 		rs; 	// rs.item will become a real number

  	initial begin
      st = new;
      bs = new;
      rs = new;

      // Assign different values, and add 10 to these values
      // Then print the result - Note the different values printed
      // that are affected by change in data type
      st.item = -456;
      $display ("st.item = %0d", st.add_a (10));

      bs.item = 8'hA1;
      $display ("bs.item = %0d", bs.add_a (10));

      rs.item = 3.14;
      $display ("rs.item = %0.2f", rs.add_a (10));
    end
endmodule
