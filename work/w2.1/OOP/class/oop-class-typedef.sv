typedef shortint unsigned u_shorti;
typedef enum {RED, YELLOW, GREEN} e_light;
typedef bit [7:0] ubyte;

typedef class DEF;  // Inform compiler that DEF might be
                    // used before actual class definition

typedef XYZ;        // legal; typedef XYZ is declared to be of type class
                    // which is later proved to be the same. It is not 
                    // necessary to specify that XYZ is of type class 
                    // in the typedef statement

class ABC;
	DEF def;        // Okay: Compiler knows that DEF
	                // declaration will come later
endclass

class DEF;
	ABC abc;
endclass

module tb;

  initial begin
	XYZ #(8'h3f, real)              xyz0;   // positional parameter override
	XYZ #(.ADDR(8'h60), .T(real))   xyz1;  	// named parameter override

    u_shorti 	data = 32'hface_cafe;
    e_light 	light = GREEN;
    ubyte 		cnt = 8'hFF;

    $display ("light=%s data=0x%0h cnt=%0d", light.name(), data, cnt);
  end
    
endmodule

class XYZ #(parameter ADDR = 8'h00, type T = int);  // typedef can also be
                                                    // used on classes with a
                                                    // parameterized port list
endclass
