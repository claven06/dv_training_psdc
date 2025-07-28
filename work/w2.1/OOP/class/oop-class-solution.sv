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

    task set_header (bit[2:0] header);
        this.header = header;
    endtask

    function bit[2:0] get_header ();
        return header;
    endfunction

	function display ();
		$display ("Header = 0x%0h, Encode = %0b, Mode = 0x%0h, Stop = %0b",
		           this.header, this.encode, this.mode, this.stop);
	endfunction
endclass

module tb_top;
	myPacket pkt0, pkt1, class_1;   // creating handle
    int y;
    bit[2:0] header;

	initial begin
		pkt0 = new (3'h2, 3'h3);    // creating object for handle
		pkt0.display ();            // accessing class method

		pkt1 = new ();              // creating object for handle
		pkt1.display ();            // accessing class method

        class_1 = new();            // creating handle and object
        class_1.set(84);            // accessing class method

        y = class_1.get();          //accessing class method
        $display("y=%0d", y);

        pkt1.set_header(3'h3);
        header = pkt1.get_header();
        $display("header=%0h", header);

	end
endmodule

//Exercise
//1. Write a task/function to set & get header and display the header value.
//
