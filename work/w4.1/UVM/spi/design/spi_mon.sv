class spi_mon extends uvm_monitor;
  `uvm_component_utils(spi_mon)

  virtual spi_if vif;
  uvm_analysis_port #(spi_tran) mon_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mon_ap = new("mon_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF", "Virtual interface for monitor not set")
    end
  endfunction


  task run_phase(uvm_phase phase);
    spi_tran tr;

    forever begin
      @(posedge vif.mon_cb.start);

      tr = spi_tran::type_id::create("tr", this);

      tr.start   = vif.mon_cb.start;
      tr.tx_data = vif.mon_cb.tx_data;

      wait (vif.mon_cb.done == 1);

      // Capture end-of-transfer values
      tr.rx_data = vif.mon_cb.rx_data;
      tr.done    = vif.mon_cb.done;
      tr.busy    = vif.mon_cb.busy;
      tr.sclk    = vif.mon_cb.sclk;
      tr.mosi    = vif.mon_cb.mosi;
      tr.miso    = vif.mon_cb.miso;
      tr.cs_n    = vif.mon_cb.cs_n;

      mon_ap.write(tr);

      `uvm_info("SPI_MON", $sformatf(
        "Captured transaction: start=%0b tx_data=0x%0h rx_data=0x%0h",
        tr.start, tr.tx_data, tr.rx_data
      ), UVM_MEDIUM);
    end
  endtask
endclass
