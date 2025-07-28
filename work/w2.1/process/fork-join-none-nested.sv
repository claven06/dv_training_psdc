module tb;
	initial begin
      $display ("[%0t] Main Thread: Fork join going to start", $time);
		fork
          begin
			fork
              print (20, "Thread1_0");
              print (30, "Thread1_1");
            join_none
            $display("[%0t] Nested fork has finished", $time);
          end
          print (10, "Thread2");
        join_none
      $display ("[%0t] Main Thread: Fork join has finished", $time);
	end

  // Note that we need automatic task
  task automatic print (int _time, string t_name);
    #(_time) $display ("[%0t] %s", $time, t_name);
  endtask
endmodule
