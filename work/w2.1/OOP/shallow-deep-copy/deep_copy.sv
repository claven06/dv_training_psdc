//
//Deep-Copy: everything (including nested objects) is copied and typically 
//custom code, e.g. copy() is required for this purpose.
//
//Note that we have invoked the custom copy() function here instead of the 
//shallow copy method, and hence Header object contents are expected to be 
//copied into p2 as well.
//
//Note that id of object p2 still holds onto the previous value even though 
//p1's id field was changed.
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

    function copy (Packet p);
      this.addr = p.addr;
      this.data = p.data;
      this.hdr.id = p.hdr.id;
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
		
		// Deep copy p1 into p2; p2 is a new object with contents in p1
		p2 = new (1,2,3);   //given some values
        p2.display("p2");
		p2.copy(p1);
		p2.display ("p2");
		
		// Now let's change the addr, data and id in p1
		p1.addr = 32'habcd_ef12;
		p1.data = 32'h5a5a_5a5a;
		p1.hdr.id = 17;
		p1.display ("p1");
		
		// Print p2 and see that hdr.id 
		// addr and data remain unchanged.
		p2.display ("p2");
	end
endmodule
