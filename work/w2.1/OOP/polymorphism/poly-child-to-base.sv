class Packet;
    int addr;

    function new (int addr);
        this.addr = addr;
    endfunction

    // Here the function is declared as "virtual"
    // so that a different definition can be given
    // in any child class
    //virtual function void display ();   //with virtual keyword
	function void display ();           //without virtual keyword
		$display ("[Base] addr=0x%0h", addr);
	endfunction
endclass

// A subclass called 'ExtPacket' is derived from the base class 'Packet' using
// 'extends' keyword which makes 'ExtPacket' a child of the parent class 'Packet'
// The child class inherits all variables and methods from the parent class
class ExtPacket extends Packet;

	// This is a new variable only available in child class
	int data;

    function new (int addr, data);
        super.new (addr); 	// Calls 'new' method of parent class
        this.data = data;
    endfunction

	function void display ();
		$display ("[Child] addr=0x%0h data=0x%0h", addr, data);
	endfunction
endclass

module tb;
	Packet      bc; 	// bc stands for BaseClass
	ExtPacket   sc; 	// sc stands for SubClass

	initial begin
		sc = new (32'hfeed_feed, 32'h1234_5678);

		// Assign sub-class to base-class handle
		bc = sc;

		bc.display ();
		sc.display ();

// Even though bc points to the child class instance, when display() function
// is called from bc it still invoked the display() function within the 
// base class. This is because the function was called based on the type of 
// the handle instead of the type of object the handle is pointing to. 
// Now let's try to reference a subclass member via a base class handle for 
// which you'll get a compilation error.
  
        // Print variable in sub-class that is pointed to by
        // base class handle
		//$display ("data=0x%0h", bc.data);
	end
endmodule

