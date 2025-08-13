covergroup cg_inputs @(posedge clk);
  
  req_cp: coverpoint req {
    bins req_00  = {2'b00};
    bins req_01   = {2'b01};
    bins req_10   = {2'b10};
    bins req_11 = {2'b11};
  }
  
  wait_cp: coverpoint wait_duration {
    bins short_wait = {[8'h00:8'h55]};
    bins med_wait   = {[8'h56:8'hAA]};
    bins long_wait  = {[8'hAB:8'hFF]};
  }

  din_master_cp: coverpoint din_master {
    bins low_values  = {[8'h00 : 8'h55]};
    bins mid_values  = {[8'h56 : 8'hAA]};
    bins high_values = {[8'hAB : 8'hFF]};
  }

  din_slave_cp: coverpoint din_slave {
    bins low_values  = {[8'h00 : 8'h55]};
    bins mid_values  = {[8'h56 : 8'hAA]};
    bins high_values = {[8'hAB : 8'hFF]};
  }

  dout_master_cp: coverpoint dout_master iff (done_rx){
    bins low_values  = {[8'h00 : 8'h55]};
    bins mid_values  = {[8'h56 : 8'hAA]};
    bins high_values = {[8'hAB : 8'hFF]};
  }

  dout_slave_cp: coverpoint dout_slave iff (done_tx){
    bins low_values  = {[8'h00 : 8'h55]};
    bins mid_values  = {[8'h56 : 8'hAA]};
    bins high_values = {[8'hAB : 8'hFF]};
  }

  done_tx_cp: coverpoint done_tx {
    bins zero  = {0};
    bins one  = {1};
  }

  done_rx_cp: coverpoint done_rx {
    bins zero  = {0};
    bins one  = {1};
  }  
  
  // Cross coverage
  cp_req_req_01_X_din_master: cross req_cp, din_master_cp {
      bins req_01_x_low_din_master = binsof(req_cp.req_01) && binsof (din_master_cp.low_values);
      bins req_01_x_mid_din_master = binsof(req_cp.req_01) && binsof (din_master_cp.mid_values);
      bins req_01_x_high_din_master = binsof(req_cp.req_01) && binsof (din_master_cp.high_values);
  }

  cp_req_req_10_X_din_slave: cross req_cp, din_slave_cp {
      bins req_10_x_low_din_slave = binsof(req_cp.req_10) && binsof (din_slave_cp.low_values);
      bins req_10_x_mid_din_slave = binsof(req_cp.req_10) && binsof (din_slave_cp.mid_values);
      bins req_10_x_high_din_slave = binsof(req_cp.req_10) && binsof (din_slave_cp.high_values);
  }

  cp_req_req_11_X_din_slave: cross req_cp, din_slave_cp{
      bins req_11_x_low_din_slave = binsof(req_cp.req_11) && binsof (din_slave_cp);
  }

  cp_req_req_11_X_din_master: cross req_cp, din_master_cp {
      bins req_11_x_low_din_slave = binsof(req_cp.req_11) && binsof (din_master_cp);
  }

  cp_done_tx_X_din_master_X_dout_slave: cross done_tx_cp, din_master_cp, dout_slave_cp{
      bins one_X_low_din_master_X_dout_slave = binsof (done_tx_cp.one) && binsof (din_master_cp.low_values) && binsof (dout_slave_cp.low_values);
      bins one_X_mid_din_master_X_dout_slave = binsof (done_tx_cp.one) && binsof (din_master_cp.mid_values) && binsof (dout_slave_cp.mid_values);
      bins one_X_high_din_master_X_dout_slave = binsof (done_tx_cp.one) && binsof (din_master_cp.high_values) && binsof (dout_slave_cp.high_values);
      ignore_bins others_low  = binsof(done_tx_cp.one) &&
                              binsof(din_master_cp.low_values) &&
                              !binsof(dout_slave_cp.low_values);

      ignore_bins others_mid  = binsof(done_tx_cp.one) &&
                              binsof(din_master_cp.mid_values) &&
                              !binsof(dout_slave_cp.mid_values);

      ignore_bins others_high = binsof(done_tx_cp.one) &&
                              binsof(din_master_cp.high_values) &&
                              !binsof(dout_slave_cp.high_values);
      ignore_bins others_done_not_one = !binsof(done_tx_cp.one);      
  }

  cp_done_rx_X_din_slave_X_dout_master: cross done_rx_cp, din_slave_cp, dout_master_cp{
      bins one_X_low_din_slave_X_dout_master = binsof (done_rx_cp.one) && binsof (din_slave_cp.low_values) && binsof (dout_master_cp.low_values);
      bins one_X_mid_din_slave_X_dout_master = binsof (done_rx_cp.one) && binsof (din_slave_cp.mid_values) && binsof (dout_master_cp.mid_values);
      bins one_X_high_din_slave_X_dout_master = binsof (done_rx_cp.one) && binsof (din_slave_cp.high_values) && binsof (dout_master_cp.high_values);
      ignore_bins others_low  = binsof(done_rx_cp.one) &&
                              binsof(din_slave_cp.low_values) &&
                              !binsof(dout_master_cp.low_values);

      ignore_bins others_mid  = binsof(done_rx_cp.one) &&
                              binsof(din_slave_cp.mid_values) &&
                              !binsof(dout_master_cp.mid_values);

      ignore_bins others_high = binsof(done_rx_cp.one) &&
                              binsof(din_slave_cp.high_values) &&
                              !binsof(dout_master_cp.high_values);
      ignore_bins others_done_not_one = !binsof(done_rx_cp.one); 
  }

endgroup


cg_inputs cov_inst = new();
