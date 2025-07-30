//
//inline constraint
//Consider that a class already has well written constraints and there is a 
//need to randomize the class variables with a set of different constraints 
//decided by the user. By using the with construct, users can declare 
//in-line constraints at the point where the randomize() method is called. 
//These additional constraints will be considered along with the object's 
//original constraints by the solver.
//

class Item;
  rand bit [7:0] id;

  constraint c_id { id < 25; }

endclass

module tb;

  initial begin
    Item pkt = new ();
    pkt.randomize() with { id == 10; }; // Inline constraint using with construct
    $display ("Item Id = %0d", pkt.id);
  end
endmodule
