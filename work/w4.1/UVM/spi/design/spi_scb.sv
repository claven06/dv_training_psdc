class spi_scb extends uvm_scoreboard;
  `uvm_component_utils(spi_scb)

  uvm_analysis_imp#(spi_tran, spi_scb) scb_imp;
  virtual spi_if vif;

  // Internal tracking variables
  bit busy_prev, done_prev, start_prev;
  int busy_cycle_count;
  bit in_transaction;
  // For tracking data during transaction
  bit [7:0] mosi_bits [$];  // FIFO of bits shifted on MOSI
  bit [7:0] miso_bits [$];  // FIFO of bits sampled from MISO

  bit [7:0] tx_expected; // Expected TX (from sequence/tran)
  bit [7:0] rx_expected; // Expected RX (SLAVE_RESET_RESPONSE or calculated)
  bit [7:0] rx_captured; // Actual RX captured at done
      static bit last_mosi;
      static bit [7:0] last_rx_data;

time prev_sclk_edge, curr_sclk_edge;
real measured_period;
  int CLK_DIV = 4;                  // Example: match DUT parameter
  real clk_period = 10ns;           // Base clk period
  real expected_sclk_period;        // Computed

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
  fork
	  forever begin
      @(posedge vif.clk);
      // (A) start during busy
      if (vif.start && vif.busy) begin
        `uvm_error("PROTO", "Start asserted while busy=1 (should be ignored)")
      end

      // (B) Busy goes high immediately after start
      if (!vif.start && start_prev) begin
        if (!vif.busy)
          `uvm_error("PROTO", "Busy did not assert immediately after start")
        else begin
		in_transaction = 1;
		busy_cycle_count = 0;
		end
	  end

      // (D) Busy should last exactly 8 bits
      if (busy_prev && !vif.busy) begin
		//$display("busy ended, count=%0d", busy_cycle_count);
        if (busy_cycle_count != 8)
          `uvm_error("PROTO", $sformatf(
            "Busy lasted %0d cycles, expected 8", busy_cycle_count
          ))
        in_transaction = 0;
		busy_cycle_count = 0;
      end
	 
	end

   forever begin
	  @(posedge vif.clk);
      // (E) Done pulse = exactly 1 clock cycle
      if (vif.done && !done_prev) begin
		@(posedge vif.clk);
        if (vif.done)
          `uvm_error("PROTO", "Done should be 1 cycle only");
      end
   end

	forever begin
	  @(posedge vif.clk);
      // (F) Busy deasserts 1 cycle after done
      if (vif.done && !done_prev) begin
    	@(posedge vif.clk);
        if (vif.busy)
          `uvm_error("PROTO", "Busy did not deassert 1 cycle after done");
      end

      // Update previous values
      start_prev = vif.start;
      busy_prev  = vif.busy;
      done_prev  = vif.done;
	end
	

	  forever begin
		@(posedge vif.sclk iff vif.busy);
		busy_cycle_count++;
	  end
//*******************TEST_2*************************************
	forever begin
      // 2.A.a Correct Bit Order check (MSB first on MOSI)
	  @(posedge vif.sclk iff vif.busy); // wait for rising sclk while busy
      if (vif.sclk && vif.busy) begin
        // Track MOSI bits on SCLK rising edge
		
        mosi_bits.push_back(vif.mosi);
        if (mosi_bits.size() == 8) begin
          if (mosi_bits[0] != vif.tx_data[7] ||
              mosi_bits[7] != vif.tx_data[0]) begin
            `uvm_error("DATA", $sformatf("MOSI bit order incorrect: expected MSB=%0b LSB=%0b, got MSB=%0b LSB=%0b",
                         vif.tx_data[7], vif.tx_data[0], mosi_bits[0], mosi_bits[7]))
          end
        end
      end

      // 2.A.b MOSI changes only on SCLK rising edge

      if (!vif.sclk && vif.busy) begin
        if (vif.mosi != last_mosi) begin
          `uvm_error("DATA", "MOSI changed when SCLK was low! Must only change on rising edge")
        end
      end
      last_mosi = vif.mosi;

      // 2.B.a MISO sampled only on falling SCLK edge
      if (!vif.sclk && vif.busy) begin
        miso_bits.push_back(vif.miso);
      end

      // 2.B.b Compare RX data to expected slave response
      if (vif.done) begin
        rx_captured = {>>{miso_bits[0]}}; // pack bits MSB first
        if (rx_captured !== vif.rx_data) begin
          `uvm_error("DATA", $sformatf("RX data mismatch: expected %h, got %h",
                        vif.rx_data, rx_captured))
        end
        miso_bits.delete();
        mosi_bits.delete();
      end

      // 2.B.c Ensure rx_data updates only on done=1

      if (!vif.done && vif.busy && vif.rx_data !== last_rx_data) begin
        `uvm_error("DATA", "RX data changed mid-transfer! Must update only when done pulses")
      end
      last_rx_data = vif.rx_data;
	end
//********************************TEST_3****************************************

  // 3.A Clock Frequency Check
    // On every sclk edge, measure period
	forever begin
	  @(posedge vif.sclk);
	  if (prev_sclk_edge != 0) begin
		time period = $time - prev_sclk_edge;
		if (period != 2*CLK_DIV*clk_period)
		  `uvm_error("SPI_SCB", $sformatf("SCLK period mismatch: %0t (expected %0t)", period, 2*CLK_DIV*clk_period));
	  end
	  prev_sclk_edge = $time;
	
	end

	forever begin
	@(posedge vif.clk);
	// Reset when idle or after done
	if (vif.cs_n || vif.done) begin
	  prev_sclk_edge = 0;
	end

    // 3.C Idle State Check (CPOL=0)
    if (vif.start == 0 && vif.cs_n) begin
      if (vif.sclk !== 1'b0) begin
        `uvm_error("SCLK_IDLE", "SCLK not low during idle (CPOL=0, cs_n=1)")
      end
  
    end
	end

  join_none
  endtask
endclass

