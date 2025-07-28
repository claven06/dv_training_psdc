class ABC;
	rand bit [3:0] 	m_var;

	// Inverted inside: Constrain m_var to be outside 3 to 7
	constraint c_var { !(m_var inside {[3:7]}); }
endclass

module tb;
	initial begin
		ABC abc = new();
		repeat (5) begin
			abc.randomize();
			$display("abc.m_var = %0d", abc.m_var);
		end

	end
endmodule
