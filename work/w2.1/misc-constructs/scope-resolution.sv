//
//scope resolution operator ::
//
class ABC;
	int     	data;
    static int  sdata; 

	extern virtual function void display();

    static function void print();
        $display("sdata = 0x%0h", sdata);
    endfunction

endclass

// Definition of an external function using scope
// resolution operator
function void ABC::display();
	$display("data = 0x%0h", data);
endfunction

module tb;
	initial begin
        ABC a1, a2;

		ABC abc = new();
		abc.data = 32'hface_cafe;
		abc.display();

      	// Assign to static variable before creating
      	// class objects, and display using class_type and
      	// scope resolution operator
		ABC::sdata = 32'hface_face;
		ABC::print();

      	a1 = new();
      	a2 = new();
      	$display ("a1.sdata=0x%0h a2.sdata=0x%0h", a1.sdata, a2.sdata);

	end
endmodule
