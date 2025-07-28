module tb;

  // Create event variables
  event event_a, event_b;

  initial begin
    // Comment code below and try again to see Thread2 finish later
    event_b = event_a;
    $display("[T=%0t] initial begin: setting event_b = event_a",$time);

    fork
      // Thread1: waits for event_a to be triggered
      begin
        wait(event_a.triggered);
        $display ("[T=%0t] Thread1: Wait for event_a is over", $time);
      end

  	  // Thread2: waits for event_b to be triggered
      begin
        wait(event_b.triggered);
        $display ("[T=%0t] Thread2: Wait for event_b is over", $time);
      end

      // Thread3: triggers event_a at 20ns
      begin
        #20 ->event_a;
        $display("[T=%0t] Thread3: event_a triggered",$time);
      end

      // Thread4: triggers event_b at 30ns
      begin
        #30 ->event_b;
        $display("[T=%0t] Thread4: event_b triggered",$time);
      end

      // Thread5: Assigns event_b to event_a at 10ns
      begin
        // Comment code below and try again to see Thread2 finish later
//        #10 event_b = event_a;
//        $display("[T=%0t] Thread5: setting event_b = event_a",$time);
      end
    join
    $display("[T=%0t] end of fork-join",$time);
  end
endmodule
