//
//A compilation error will be reported since 
//abstract classes are not allowed to be instantiated.
//
virtual class BaseClass;
//class BaseClass;
	int data;

	function new();
		data = 32'hc0de_c0de;
	endfunction
endclass

//extend abstract classes to form other classes that can be instantiated 
//using new() method.
class ChildClass extends BaseClass;
	function new();
		data = 32'hfade_fade;
	endfunction
endclass

module tb;
//	BaseClass base;
    ChildClass child;
	initial begin
//		base = new();
    	child = new();
//		$display ("data=0x%0h", base.data);
		$display ("data=0x%0h", child.data);
	end
endmodule
