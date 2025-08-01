module testbench;
  bit tb_clk;

  clk_if 	m_clk_if();
  adder_if 	m_adder_if();
  my_adder8	dut0(m_adder_if);   //Design Under Test

  initial begin
    test t0;

    t0 = new();
    t0.e0.m_adder_vif = m_adder_if;
    t0.e0.m_clk_vif = m_clk_if;
    t0.run();

    // Once the main stimulus is over, wait for some time
    // until all transactions are finished and then end
    // simulation. Note that $finish is required because
    // there are components that are running forever in
    // the background like clk, monitor, driver, etc
    #50 $finish;
  end
endmodule
