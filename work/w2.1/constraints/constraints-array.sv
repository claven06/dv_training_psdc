//
//we declare a dynamic array as indicated by the empty square brackets [] 
//of type rand. A constraint is defined to limit the size of the dynamic array 
//to be somewhere in between 5 and 10. Another constraint is defined to assign 
//each element in the array with the value of its index.
//
class Packet;
  rand bit [3:0] 	d_array []; 	// Declare a dynamic array with "rand"

  // Constrain size of dynamic array between 5 and 10
  constraint c_array { d_array.size() > 5; d_array.size() < 10; }

  // Constrain value at each index to be equal to the index itself
  constraint c_val   { foreach (d_array[i])
    					d_array[i] == i;
                     }

  // Utility function to display dynamic array contents
  function void display();
    foreach (d_array[i])
      $display ("d_array[%0d] = 0x%0h", i, d_array[i]);
  endfunction
endclass

module tb;
  Packet pkt;

  // Create a new packet, randomize it and display contents
  initial begin
    pkt = new();
    pkt.randomize();
    pkt.display();
  end
endmodule
