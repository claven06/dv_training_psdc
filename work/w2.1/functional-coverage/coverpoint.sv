
// Coverpoints
//
// The example shown below randomizes the two variables, mode and cfg multiple 
// times and is assigned a value on every negative edge of the clock. The 
// covergroup is specified to be sampled at every occurence of a positive edge 
// of the clock. The two variables are randomized 5 times at the negative 
// edge of the clock and sampled at the positive edge of the clock.
//

module tb;

  bit [1:0] mode;
  bit [2:0] cfg;

  bit clk;
  always #20 clk = ~clk;

  // "cg" is a covergroup that is sampled at every posedge clk
  // This covergroup has two coverage points, one to cover "mode"
  // and the other to cover "cfg". Mode can take any value from
  // 0 -> 3 and cfg can take any value from 0 -> 7
  covergroup cg @ (posedge clk);
    // Coverpoints can optionally have a name before a colon ":"
    cp_mode    : coverpoint mode;
    cp_cfg_10  : coverpoint cfg[1:0];
    cp_cfg_lsb : coverpoint cfg[0];
    cp_sum     : coverpoint (mode + cfg);
  endgroup

  cg  cg_inst;

  initial begin
    cg_inst= new();

    cg_inst.set_inst_name("mode-cfg_cov");
//    cg_inst.start();    //Begins coverage collection
    for (int i = 0; i < 5; i++) begin
      @(negedge clk);
      mode = $random;
      cfg  = $random;
      $display ("[%0t] mode=0x%0h cfg=0x%0h", $time, mode, cfg);
    end
  end

  initial begin
    #500 
//    cg_inst.stop();    //ends coverage collection
    $display ("Instance Coverage = %0.2f %%", cg_inst.get_inst_coverage());
    $display ("Cumulative Coverage = %0.2f %%", cg_inst.get_coverage());
    $finish;
  end
endmodule
