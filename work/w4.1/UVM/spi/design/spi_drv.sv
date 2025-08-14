class driver #( int ADDR_WIDTH, int DATA_WIDTH );
  virtual switch_if #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH)) m_switch_vif;
  virtual clk_if                                                        m_clk_vif;
  event drv_done;
  mailbox drv_mbx;

  task run();
    $display ("T=%0t [Driver] starting ...", $time);

    // Try to get a new transaction every time and then assign
    // packet contents to the interface. But do this only if the
    // design is ready to accept new transactions
    forever begin
      Packet #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH)) item;

      $display ("T=%0t [Driver] waiting for item ...", $time);
      drv_mbx.get(item);
      $display ("T=%0t [Driver] retrieved item...", $time);
      @ (posedge m_clk_vif.tb_clk);
	  item.print("Driver");
      m_switch_vif.rstn <= item.rstn;
      m_switch_vif.vld <= item.vld;
      m_switch_vif.addr <= item.addr;
      m_switch_vif.data <= item.data;

      $display("T=%0t [Driver] trigger the drv_done event", $time);
      ->drv_done;
    end
  endtask
endclass
