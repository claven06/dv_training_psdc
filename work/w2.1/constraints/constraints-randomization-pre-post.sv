class myClass;
  rand bit [7:0]	cnt_id;

  constraint c_cnt_id { cnt_id >= 10;
                        cnt_id <= 50; };

  function void pre_randomize ();
  	$display ("This will be called just before randomization");
  endfunction

  function void post_randomize ();
  	$display ("This will be called just after randomization");
  endfunction

endclass

module tb;
    myClass pkt;

    initial begin
      pkt = new ();
      $display ("Initial cnt_id = %0d", pkt.cnt_id);
      if (pkt.randomize ())
      	$display ("Randomization successful !");
      $display ("After randomization cnt_id = %0d", pkt.cnt_id);
    end
endmodule
