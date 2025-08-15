class spi_scb extends uvm_scoreboard;
  `uvm_component_utils(spi_scb)

  uvm_analysis_imp#(spi_tran, spi_scb) scb_imp;
  virtual spi_if vif;

  // Internal tracking variables
  bit busy_prev, done_prev, start_prev;
  int busy_cycle_count;
  bit in_transaction;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    scb_imp = new("scb_imp", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    if (!uvm_config_db#(virtual spi_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NOVIF", "Virtual interface for scoreboard not set")
    end
  endfunction

  function void write(spi_tran tr);
    `uvm_info("SPI_SCB", $sformatf(
      "Transaction received: start=%0b tx_data=0x%0h rx_data=0x%0h",
      tr.start, tr.tx_data, tr.rx_data
    ), UVM_LOW);
  endfunction

  task run_phase(uvm_phase phase);
    forever begin
      @(posedge vif.clk);

      // (A) start during busy
      if (vif.mon_cb.start && vif.mon_cb.busy) begin
        `uvm_error("PROTO", "Start asserted while busy=1 (should be ignored)")
      end

      // (B) Busy goes high immediately after start
      if (vif.mon_cb.start && !start_prev) begin
        if (!vif.mon_cb.busy)
          `uvm_error("PROTO", "Busy did not assert immediately after start")
        else begin
          busy_cycle_count = 0;
          in_transaction = 1;
        end
      end

      // (C) Count busy cycles
      if (in_transaction && vif.mon_cb.busy)
        busy_cycle_count++;

      // (D) Busy should last exactly 8 bits
      if (busy_prev && !vif.mon_cb.busy) begin
        if (busy_cycle_count != 8)
          `uvm_error("PROTO", $sformatf(
            "Busy lasted %0d cycles, expected 8", busy_cycle_count
          ));
        in_transaction = 0;
      end

      // (E) Done pulse = exactly 1 clock cycle
      if (vif.mon_cb.done && !done_prev) begin
        @(posedge vif.clk);
        if (vif.mon_cb.done)
          `uvm_error("PROTO", "Done should be 1 cycle only");
      end

      // (F) Busy deasserts 1 cycle after done
      if (vif.mon_cb.done && !done_prev) begin
        @(posedge vif.clk);
        if (vif.mon_cb.busy)
          `uvm_error("PROTO", "Busy did not deassert 1 cycle after done");
      end

      // Update previous values
      start_prev = vif.mon_cb.start;
      busy_prev  = vif.mon_cb.busy;
      done_prev  = vif.mon_cb.done;
    end
  endtask
endclass

