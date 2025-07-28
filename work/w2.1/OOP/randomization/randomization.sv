class myPacket;

	// Declare two variables for randomization
	// mode is of type rand and hence any random value between 0 and 3 can be picked each time
	// key is of type randc and hence random values between 0 and 7 can be picked and
	// values will be repeated only after all other values have been already taken
	rand   bit [1:0]    mode;
	randc  bit [2:0]    key;

	// These statements are called constraints that help us to limit
	// the randomness within specified ranges
	// mode is constrained to have a value less than 3 (excluding)
	// key is constrained to have a value between 2 and 7 (excluding)
	constraint c_mode1 { mode < 3; }
	constraint c_key1  { key > 2;
                         key < 7; }

    // This is just a function to display current values of these variables
    function display ();
       $display ("Mode : 0x%0h Key : 0x%0h", mode, key);
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
//
//Notice that randomization of Mode has resulted in repetitive values, while 
//for Key, the values are cyclic in nature (3,4,5,6 is a complete set).
//
