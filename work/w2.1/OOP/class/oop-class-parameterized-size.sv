// A class is parameterized by #()
// Here, we define a parameter called "size" and gives it
// a default value of 8. The "size" parameter is used to
// define the size of the "out" variable
class something #(int size = 8);
	bit [size-1:0] out;
endclass

module tb;

  // Override default value of 8 with the given values in #()
  something  #(16) sth1;                 // pass 16 as "size" to this class object
  something  #(.size (8)) sth2;          // pass 8 as "size" to this class object
  typedef something #(4) td_nibble;      // create an alias for a class with "size" = 4 as "nibble"
  td_nibble nibble;

  initial begin
    // 1. Instantiate class objects
    sth1 = new;
    sth2 = new;
  	nibble = new;

    // 2. Print size of "out" variable. $bits() system task will return
    // the number of bits in a given variable
    $display ("sth1.out   = %0d bits", $bits(sth1.out));
    $display ("sth2.out   = %0d bits", $bits(sth2.out));
    $display ("nibble.out = %0d bits", $bits(nibble.out));
  end
endmodule
