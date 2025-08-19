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
      bins value  = {8'hB9};
      bins zero  = {0};
    }

    slave_tx_data_cp : coverpoint item.slave_tx_data {
      bins value  = {8'hB9};
      bins zero  = {0};
    }

    slave_rx_data_cp : coverpoint item.slave_rx_data {
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
    
    done_x_tx_slaverx_cp : cross done_cp, tx_data_cp, slave_rx_data_cp {
      bins low = binsof (done_cp.one) && binsof (tx_data_cp.low) &&  binsof (slave_rx_data_cp.low);
      bins mid = binsof (done_cp.one) && binsof (tx_data_cp.mid) &&  binsof (slave_rx_data_cp.mid);
      bins high = binsof (done_cp.one) && binsof (tx_data_cp.high) &&  binsof (slave_rx_data_cp.high);

      ignore_bins others_low = binsof (done_cp.one) && binsof (tx_data_cp.low) && !binsof (slave_rx_data_cp.low);
      ignore_bins others_mid = binsof (done_cp.one) && binsof (tx_data_cp.mid) && !binsof (slave_rx_data_cp.mid);
      ignore_bins others_high = binsof (done_cp.one) && binsof (tx_data_cp.high) && !binsof (slave_rx_data_cp.high);
      ignore_bins others_done_not_one = !binsof(done_cp.one);
    }

    done_x_slavetx_rx_cp : cross done_cp, slave_tx_data_cp, rx_data_cp {
      bins value = binsof (done_cp.one) && binsof (slave_tx_data_cp.value) &&  binsof (rx_data_cp.value);
      ignore_bins others_value = binsof (done_cp.one) && binsof (slave_tx_data_cp.value) && !binsof (rx_data_cp.value);
      ignore_bins others_done_not_one = !binsof(done_cp.one);
    }


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