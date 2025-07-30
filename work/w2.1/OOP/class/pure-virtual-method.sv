virtual class BaseClass;
	int data;

	pure virtual function int getData();
endclass

class ChildClass extends BaseClass;
	virtual function int getData();
		data = 32'hcafe_cafe;
		return data;
	endfunction
endclass

module tb;
	ChildClass child;
	initial begin
		child = new();
		$display ("data = 0x%0h", child.getData());
	end
endmodule
