class myPacket;
	rand   bit [7:0] mode;
	randc  bit [7:0] key;
	int  low, high;

	constraint c_simple {  mode > 2;
	                       key == 3; }

// This won't work, because it contradicts c_simple - Run-time error
//	constraint c_key    {  key < 2; }

// This won't work either, because of wrong syntax - you can't specify it this way
//  constraint c_signs  {  0 < key < 4; }

/*    constraint c_range  { key inside {[low:high]};
    					mode inside {[21:50]};
    					mode inside {23, 24, 51}; }
*/
// Choose any value other than 2,3,4,5
/*    constraint c_invert { !(key inside {[2:5]}); }
*/
// Choose 10 or 22 ; with equal probability even if 10 and 20 appeared multiple times
//    constraint c_weight { mode inside {10, 10, 10, 22, 22};}

// 4 has 50/130 chance, 43 has 10/130 chance, any value between 45:90 has 70/130 chance
//    constraint c_key_dist  { key  dist {4:=50, 43:=10, [45:90]:=70 };}

// 4 has 10/100 chance, 43 has 30/100 chance, any value between 45:47 has 20/100 chance
/*    constraint c_mode_dist { mode dist {4:/10, 43:/30, [45:47]:/60 };}
*/
    function void pre_randomize ();
       this.low = 1;
       this.high = 2;
    endfunction

    // This is just a function to display current values of these variables
    function display ();
       $display ("Mode : %0d Key : %0d", mode, key);
    endfunction

endclass

module tb_top;

	// Create a class object handle
	myPacket pkt;

	initial begin

		// Instantiate the object, and allocate memory to this variable
		pkt = new ();

		// Let's just randomize the class object 15 times and display all the
		// values randomization yielded each time
		for (int i = 0; i < 15; i++) begin

			// By using assert(), we are ensuring that randomization is successful.
			assert (pkt.randomize ());
			pkt.display ();
		end
	end
endmodule
