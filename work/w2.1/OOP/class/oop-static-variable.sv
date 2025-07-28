//
//When a variable inside a class is declared as static, that variable will be
//the only copy in all class instances. To demonstrate an example we'll compare
//a static counter vs a non-static counter. The static counter is declared with
//static keyword and named as static_ctr while the normal counter variable is 
//named as ctr. Both counters will be incremented within the new() function so
//that they are updated everytime an object is created.
//
//You'll see that the static counter is shared between all class objects p1, p2
//and p3 and hence will increment to 3 when three packets are created. On the 
//other hand, the normal counter variable ctr is not declared as static and 
//hence every class object will have its own copy. This is the reason why ctr 
//is still 1 after all three objects are created.
//
class Packet;
	bit [15:0] 	addr;
	bit [7:0] 	data;
	static int 	static_ctr = 0;
		   int 	ctr = 0;

	function new (bit [15:0] ad, bit [7:0] d);
		addr = ad;
		data = d;
		static_ctr++;
		ctr++;
		$display ("static_ctr=%0d ctr=%0d addr=0x%0h data=0x%0h", static_ctr, ctr, addr, data);
	endfunction
endclass

module tb;
	initial begin
		Packet 	p1, p2, p3;
		p1 = new (16'hdead, 8'h12);
		p2 = new (16'hface, 8'hab);
		p3 = new (16'hcafe, 8'hfc);
	end
endmodule
