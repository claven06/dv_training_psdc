class spi_cov extends uvm_component;
  `uvm_component_utils(spi_cov)

  // Analysis imp for connecting monitor -> coverage
  uvm_analysis_imp #(spi_tran, spi_cov) cov_imp;

  // Variable to store the transaction
  spi_tran item;

  // Covergroup (remove the clocking on item.clk, use transaction sampling instead)
  covergroup spi_cg;
    option.per_instance = 1;

    tx_data_cp : coverpoint item.tx_data {
      bins low  = {[0:63]};
      bins mid  = {[64:191]};
      bins high = {[192:255]};
    }

    rx_data_cp : coverpoint item.rx_data {
      bins low  = {[0:63]};
      bins mid  = {[64:191]};
      bins high = {[192:255]};
    }

    start_cp : coverpoint item.start { bins zero = {0}; bins one = {1}; }
    busy_cp  : coverpoint item.busy  { bins zero = {0}; bins one = {1}; }
    done_cp  : coverpoint item.done  { bins zero = {0}; bins one = {1}; }
    mosi_cp  : coverpoint item.mosi  { bins zero = {0}; bins one = {1}; }
    miso_cp  : coverpoint item.miso  { bins zero = {0}; bins one = {1}; }
    cs_n_cp  : coverpoint item.cs_n  { bins zero = {0}; bins one = {1}; }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    cov_imp = new("cov_imp", this);
    spi_cg = new();
  endfunction

  // Called automatically when monitor writes
  virtual function void write(spi_tran tr_dut);
    item = tr_dut;
    spi_cg.sample();
  endfunction

endclass