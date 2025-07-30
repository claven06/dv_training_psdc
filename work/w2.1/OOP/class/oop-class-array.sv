class myPacket;
// class properties/members
	bit [2:0]  header;
	bit        encode;
	bit [2:0]  mode;
	bit [7:0]  data;
	bit        stop;
    int        x;

// methods
	function new (bit [2:0] header = 3'h1, bit [2:0] mode = 3'h5);
		this.header = header;
		this.encode = 0;
		this.mode   = mode;
		this.stop   = 1;
	endfunction

    task set (int i);
        x = i;
    endtask

    function int get ();
        return x;
    endfunction

	function display ();
		$display ("Header = 0x%0h, Encode = %0b, Mode = 0x%0h, Stop = %0b",
		           this.header, this.encode, this.mode, this.stop);
	endfunction
endclass

module tb_top;
	myPacket pkt0 [3];

	initial begin
    	for(int i = 0; i < $size (pkt0); i++) begin
   	   		pkt0[i] = new ();
       		pkt0[i].display ();
   		end
   	end
endmodule

