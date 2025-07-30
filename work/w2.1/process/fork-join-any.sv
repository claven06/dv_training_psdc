module tb_top;
   initial begin

   	  #1 $display ("[%0t ns] Start fork ...", $time);

   	  // Main Process: Fork these processes in parallel and wait until
      // any one of them finish
      fork
      	 // Thread1 : Print this statement after 5ns from start of fork
         #5 $display ("[%0t ns] Thread1", $time);

         // Thread2 : Print these two statements after the given delay from start of fork
         begin
            #2 $display ("[%0t ns] Thread2-1", $time);
            #4 $display ("[%0t ns] Thread2-2", $time);
         end

         // Thread3 : Print this statement after 10ns from start of fork
         #10 $display ("[%0t ns] Thread3", $time);
      join_any

      // Main Process: Continue with rest of statements once any of the fork-join_any is exited
      $display ("[%0t ns] After Fork-Join_any", $time);
   end
endmodule
