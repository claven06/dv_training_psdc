class myClass;
	rand bit [3:0] val;
	constraint  c1 { val > 3;
	                 val < 12; }

	constraint  c2  {val >= 10; }
endclass

module tb;
	initial begin
		for (int i = 0; i < 10; i++) begin
			myClass cls = new ();
			cls.randomize();
			$display ("itr=%0d typ=%0d", i, cls.val);
		end
	end
endmodule

//Constraint blocks are not executed from top to bottom like procedural code, 
//but are all active at the same time.
//
//Note that constraints c1 and c2 limits the val values to 10 and 11.
//
