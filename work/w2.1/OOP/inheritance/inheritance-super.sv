class Packet;
	int addr;
	function display ();
		$display ("[Base] addr=0x%0h", addr);
	endfunction
endclass

class extPacket extends Packet;
	function new ();
		super.new ();   // call base class display method
        $display("[Child] addr=0x%0h", addr);
	endfunction
endclass

module tb;
	Packet p;
  	extPacket ep;

  	initial begin
      ep = new();
      p = new();
      p.display();
    end
endmodule

