//
// Shallow-Copy copy all of the variables are copied across integers, strings, 
// instance handles, etc but nested objects are not copied entirely. Only 
// their handles will be assigned to the new object and hence both the packets 
// will point to the same nested object instance.
//
// The class Packet contains a nested class called Header. First we created 
// a packet called p1 and assigned it with some values. Then p2 was created 
// as a copy of p1 using the shallow copy method. To prove that only handles 
// and not the entire object is copied, members of the p1 packet is modified 
// including members within the nested class. When the contents in p2 are 
// printed, we can see that the id member in the nested class remains the same.
//
class Header;
	int id;
	function new (int id);
		this.id = id;
	endfunction
	
	function showId();
		$display ("id=0x%0d", id);
	endfunction
endclass

class Packet;
	int 	addr;
	int 	data;
	Header 	hdr;
	
	function new (int addr, int data, int id);
		hdr = new (id);
		this.addr = addr;
		this.data = data;
	endfunction
	
	function display (string name);
		$display ("[%s] addr=0x%0h data=0x%0h id=%0d", name, addr, data, hdr.id);
	endfunction
endclass

module tb;
	Packet p1, p2;
	initial begin
		// Create a new pkt object called p1
		p1 = new (32'hface_cafe, 32'h1234_5678, 26);
		p1.display ("p1");
		
		// Shallow copy p1 into p2; p2 is a new object with contents in p1
		p2 = new p1;
		p2.display ("p2");
		
		// Now let's change the addr, data and id in p1
		p1.addr = 32'habcd_ef12;
		p1.data = 32'h5a5a_5a5a;
		p1.hdr.id = 17;
		p1.display ("p1");
		
		// Print p2 and see that hdr.id points to the hdr in p1, while
		// addr and data remain unchanged.
		p2.display ("p2");
	end
endmodule
