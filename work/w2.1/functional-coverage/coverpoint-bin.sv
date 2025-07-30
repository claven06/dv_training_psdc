
//coverpoint bin

module tb;
  bit [2:0] mode;

  // This covergroup does not get sample automatically because
  // the sample event is missing in declaration
  covergroup cg;
    coverpoint mode {
    	bins one = {1};
    	bins five = {5};
    }
  endgroup

  // Stimulus: Simply randomize mode to have different values and
  // manually sample each time
  initial begin
    cg cg_inst = new();

    for (int i = 0; i < 5; i++) begin
	  #10 mode = $random;
      $display ("[%0t] mode = 0x%0h", $time, mode);
      cg_inst.sample(); //sample for coverage
    end
    $display ("Instance Coverage = %0.2f %%", cg_inst.get_inst_coverage());
    $display ("Cumulative Coverage = %0.2f %%", cg_inst.get_coverage());
  end

endmodule
