module testbench;
  localparam int                    LOOP        = 1000;
  localparam int                    ADDR_WIDTH  = 8;
  localparam int                    DATA_WIDTH  = 16;
  localparam bit [ADDR_WIDTH-1:0]   ADDR_DIV    = 8'h3f;
  bit tb_clk;

  clk_if 	                                                                            m_clk_if();
  switch_if #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH))                         m_switch_if_in(); 	// Interface handle inputs
  switch_if #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH))                         m_switch_if_out(); 	// Interface handle outputs

  switch	#(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH), .ADDR_DIV(ADDR_DIV))    dut0 (
    .clk(m_clk_if.tb_clk),
    .rstn(m_switch_if_in.rstn),
    .vld(m_switch_if_in.vld),
    .addr(m_switch_if_in.addr),
    .data(m_switch_if_in.data),
    .addr_a(m_switch_if_out.addr_a),
    .data_a(m_switch_if_out.data_a),
    .addr_b(m_switch_if_out.addr_b),
    .data_b(m_switch_if_out.data_b)
  );   //Design Under Test

  covergroup cg;
    cp_rstn     : coverpoint m_switch_if_in.rstn{}
    cp_vld      : coverpoint m_switch_if_in.vld{}
    cp_addr     : coverpoint m_switch_if_in.addr    {
        bins addr_equal_zero        = { 0 };
        bins addr_lesser_than_h40   = {['h1:'h3f]};
        bins addr_more_or_equal_h40 = {['h40:'hff]};
    }
    cp_data     : coverpoint m_switch_if_in.data    {
        bins data_equal_zero        = { 0 };
        bins data_equal_nonzero     = {['h1:'hffff]};
    }
    cp_addr_a   : coverpoint m_switch_if_out.addr_a {
        bins addr_equal_zero        = { 0 };
        bins addr_lesser_than_h40   = {['h1:'h3f]};
        illegal_bins addr_more_or_equal_h40 = {['h40:'hff]};
    }
    cp_data_a   : coverpoint m_switch_if_out.data_a {
        bins data_equal_zero        = { 0 };
        bins data_equal_nonzero     = {['h1:'hffff]};
    }
    cp_addr_b   : coverpoint m_switch_if_out.addr_b {
        bins addr_equal_zero        = { 0 };
        bins addr_more_or_equal_h40 = {['h40:'hff]};
        illegal_bins addr_lesser_than_h40   = {['h1:'h3f]};
    }
    cp_data_b   : coverpoint m_switch_if_out.data_b {
        bins data_equal_zero        = { 0 };
        bins data_equal_nonzero     = {['h1:'hffff]};
    }
  endgroup

  initial begin
      m_switch_if_in.rstn <= '0;
      m_switch_if_in.vld <= '0;
      m_switch_if_in.addr <= '0;
      m_switch_if_in.data <= '0;
  end

  initial begin
    test  #(.LOOP(LOOP), .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH), .ADDR_DIV(ADDR_DIV)) t0;

    cg cg_switch = new();
    t0 = new();
    t0.e0.m_switch_vif_in = m_switch_if_in;
    t0.e0.m_switch_vif_out = m_switch_if_out;
    t0.e0.m_clk_vif = m_clk_if;
    fork
      t0.run();
      forever @(posedge m_clk_if.tb_clk) cg_switch.sample();
    join_any

    // Once the main stimulus is over, wait for some time
    // until all transactions are finished and then end
    // simulation. Note that $finish is required because
    // there are components that are running forever in
    // the background like clk, monitor, driver, etc
    #50 $finish;
  end

  initial begin
    $fsdbDumpfile("dump.fsdb");
    $fsdbDumpvars;
    $fsdbDumpMDA;
  end
endmodule
