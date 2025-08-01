// The monitor has a virtual interface handle with which it can monitor
// the events happening on the interface. It sees new transactions and then
// captures information into a packet and sends it to the scoreboard
// using another mailbox.
class monitor #( int ADDR_WIDTH, int DATA_WIDTH );
  virtual switch_if #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH)) m_switch_vif;
  virtual clk_if 	                                                    m_clk_vif;

  mailbox scb_mbx; 		// Mailbox connected to scoreboard

  task run();
    $display ("T=%0t [Monitor] starting ...", $time);

    // Check forever at every clock edge to see if there is a
    // valid transaction and if yes, capture info into a class
    // object and send it to the scoreboard when the transaction
    // is over.
    forever begin
	  Packet #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH)) m_pkt = new();

      @(posedge m_clk_vif.tb_clk);
      #1;
        m_pkt.rstn   = m_switch_vif.rstn;
        m_pkt.vld    = m_switch_vif.vld;
      	m_pkt.addr   = m_switch_vif.addr;
        m_pkt.data   = m_switch_vif.data;
      	m_pkt.addr_a = m_switch_vif.addr_a;
        m_pkt.data_a = m_switch_vif.data_a;
      	m_pkt.addr_b = m_switch_vif.addr_b;
        m_pkt.data_b = m_switch_vif.data_b;
        m_pkt.print("Monitor");
      scb_mbx.put(m_pkt);
    end
  endtask
endclass
