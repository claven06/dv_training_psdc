module tb;
	// Create a new mailbox that can hold utmost 2 items
  	mailbox 	mbx = new(2);

  	// Block1: This block keeps putting items into the mailbox
  	// The rate of items being put into the mailbox is 1 every ns
  	initial begin
		for (int i=0; i < 5; i++) begin
        	$display ("[T=%0t] Thread0: Putting item #%0d, size=%0d", $time, i, mbx.num());
        	#1 mbx.put (i);
        	$display ("[T=%0t] Thread0: Put item #%0d, size=%0d", $time, i, mbx.num());
      	end
    end

  	// Block2: This block keeps getting items from the mailbox
  	// The rate of items received from the mailbox is 2 every ns
	initial begin
		forever begin
			int idx;
          	$display ("[T=%0t] Thread1: previous item #%0d, size=%0d", $time, idx, mbx.num());
			#2 mbx.get (idx);
          	$display ("[T=%0t] Thread1: Got item #%0d, size=%0d", $time, idx, mbx.num());
		end
	end
endmodule
