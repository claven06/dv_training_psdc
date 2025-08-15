class spi_drv extends uvm_driver #(spi_tran);
  `uvm_component_utils(spi_drv)

  virtual spi_if vif; // Use DRV modport for driver
      int cycle_count = 0;
      bit done_seen = 0;
  int unsigned DONE_TIMEOUT = 1000; // Number of clock cycles to wait for done

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF", "Virtual interface must be set for spi_driver (DRV modport)")
    end
  endfunction

  task run_phase(uvm_phase phase);
    spi_tran tr;

    // Wait for reset deassertion
    @(posedge vif.clk);
    wait (vif.rst_n == 1);

    forever begin
      seq_item_port.get_next_item(tr);

	  repeat (7) @(posedge vif.clk);

      // Drive transaction
      vif.drv_cb.tx_data <= tr.tx_data;
	  vif.drv_cb.miso	 <= tr.miso;

	  if (tr.start) begin
		vif.drv_cb.start <= 1'b1;
        `uvm_info(get_type_name(), $sformatf("Starting SPI transfer, TX=0x%0h", tr.tx_data), UVM_LOW)
	    @(posedge vif.clk);
	    vif.drv_cb.start <= 1'b0;
		@(posedge vif.drv_cb.done);
	  
	  end else begin
		vif.drv_cb.start <= 1'b0;
	  end

	  
      seq_item_port.item_done();
    end
  endtask
endclass

