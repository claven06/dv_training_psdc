class spi_drv extends uvm_driver #(spi_tran);
  `uvm_component_utils(spi_drv)

  virtual spi_if.drv_mp vif;

  uvm_analysis_port #(spi_tran) drv_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    drv_ap = new("drv_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual spi_if.drv_mp)::get(this, "", "vif", vif)) begin
      `uvm_error("DRIVER", "Virtual interface (drv_mp) not found in config db")
    end
   
  endfunction

  task run_phase(uvm_phase phase);
    spi_tran tr;
    forever begin
      seq_item_port.get_next_item(tr);

      @(posedge vif.clk_tb);  // Wait for the posedge clock

      `uvm_info("DRIVER", $sformatf("Drive tran to DUT: rst_n=%0b, start=%0b, tx_data=%0b, miso=%0b", tr.rst_n, tr.start, tr.tx_data, tr.miso), UVM_MEDIUM)      

      vif.rst_n_tb <= tr.rst_n;      // Drive from transaction (tr) to DUT

      repeat(7)@(posedge vif.clk_tb);
      vif.start_tb <= tr.start;
      if (tr.start === 1 ) begin
        vif.tx_data_tb <= tr.tx_data;
        repeat(1)@(posedge vif.clk_tb);
        vif.start_tb <= 1'b0;

        @(posedge vif.done_tb or posedge vif.rst_n_tb);
      end
      seq_item_port.item_done();


    end
  endtask
endclass