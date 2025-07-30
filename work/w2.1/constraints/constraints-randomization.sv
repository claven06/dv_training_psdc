//rand are standard random variables and their values are uniformly 
//distributed over their range.
//
//randc are random-cyclic and hence cycle through all the values 
//within their range before repeating any particular value.
class Packet;
	rand    bit [2:0] rand_data;
	randc   bit [2:0] randc_data;
endclass

module tb;
	initial begin
		Packet pkt = new ();
		for (int i = 0 ; i < 10; i++) begin
			pkt.randomize ();
			$display ("itr=%0d rand_data=0x%0h randc_data=0x%0h", i, 
                pkt.rand_data,pkt.randc_data);
		end
	end
endmodule

