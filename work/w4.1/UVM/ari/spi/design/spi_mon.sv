class spi_mon extends uvm_monitor;
  `uvm_component_utils(spi_mon)

  virtual spi_if.mon_mp vif;  // Use mon_mp
  virtual spi_slave_if.slv_mon_mp slave_vif;
  uvm_analysis_port #(spi_tran) mon_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mon_ap = new("mon_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual spi_if.mon_mp)::get(this, "", "vif", vif)) begin
      `uvm_error("MONITOR", "Virtual interface (mon_mp) not found in config db")
    end
    if (!uvm_config_db#(virtual spi_slave_if.slv_mon_mp)::get(this, "", "slave_vif", slave_vif))
      `uvm_fatal("MONITOR", "slave_if not set")    
  endfunction

  task run_phase(uvm_phase phase);
    spi_tran tr_dut;
    @(posedge vif.clk_tb);  // Direct clock access

    
    forever begin
    
      @(posedge vif.clk_tb);  // Direct clock access
      tr_dut = spi_tran::type_id::create("tr_dut");

      tr_dut.rst_n = vif.rst_n_tb;
      tr_dut.start = vif.start_tb;
      tr_dut.tx_data = vif.tx_data_tb;
      tr_dut.rx_data = vif.rx_data_tb;
      tr_dut.busy = vif.busy_tb;
      tr_dut.done = vif.done_tb;
      tr_dut.sclk = vif.sclk_tb;
      tr_dut.mosi = vif.mosi_tb;
      tr_dut.miso = vif.miso_tb;
      tr_dut.cs_n = vif.cs_n_tb;

      `uvm_info("MONITOR", $sformatf("Observe tran from DUT: rst_n_tb=%b, start_tb=%b, tx_data_tb=%b, miso_tb=%b >>> OUTPUT: rx_data_tb=%b, busy_tb=%b, done_tb=%b, sclk_tb=%b, mosi_tb=%b, cs_n_tb=%b",tr_dut.rst_n, tr_dut.start, tr_dut.tx_data, tr_dut.miso, tr_dut.rx_data, tr_dut.busy, tr_dut.done, tr_dut.sclk, tr_dut.mosi, tr_dut.cs_n),UVM_MEDIUM)

      //@(posedge vif.done_tb);
      tr_dut.slave_rx_data = slave_vif.slave_rx_data;
      tr_dut.slave_tx_data = slave_vif.SLAVE_RESET_RESPONSE;;

      mon_ap.write(tr_dut); //calls write func from scb
    end
  endtask
endclass