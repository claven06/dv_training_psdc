module tb;
	initial begin
      $display ("[%0t] Main Thread: Fork join going to start", $time);
		fork
			fork // Thread 1
              #50 $display ("[%0t] Thread1_0 ...", $time);
              #70 $display ("[%0t] Thread1_1 ...", $time);
              begin
                #10 $display ("[%0t] Thread1_2 ...", $time);
                #100 $display ("[%0t] Thread1_2 finished", $time);
              end
            join

			// Thread 2
          	begin
              	#5 $display ("[%0t] Thread2 ...", $time);
				#10 $display ("[%0t] Thread2 finished", $time);
            end

            // Thread 3
			#20 $display ("[%0t] Thread3 finished", $time);
		join
      $display ("[%0t] Main Thread: Fork join has finished", $time);
	end
endmodule
