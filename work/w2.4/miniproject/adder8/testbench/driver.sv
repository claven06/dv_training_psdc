class driver;
  virtual adder_if m_adder_vif;
  virtual clk_if  m_clk_vif;
  event drv_done;
  mailbox drv_mbx;

  task run();
    $display ("T=%0t [Driver] starting ...", $time);

    // Try to get a new transaction every time and then assign
    // packet contents to the interface. But do this only if the
    // design is ready to accept new transactions
    forever begin
      Packet item;

      $display ("T=%0t [Driver] waiting for item ...", $time);
      drv_mbx.get(item);
      @ (posedge m_clk_vif.tb_clk);
	  item.print("Driver");
      m_adder_vif.rstn <= item.rstn;
      m_adder_vif.a <= item.a;
      m_adder_vif.b <= item.b;

      $display("T=%0t [Driver] trigger the drv_done event", $time);
      ->drv_done;
    end
  endtask
endclass
