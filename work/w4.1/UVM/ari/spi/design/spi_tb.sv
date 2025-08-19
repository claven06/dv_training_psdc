module spi_tb;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // $time is a built-in system function
  initial $display(">>>>>>>> SIM TIME START: %0t", $time);
  final   $display(">>>>>>>> SIM TIME END  : %0t", $time);

  localparam int CLK_DIV = 4;

  bit clk_tb;
  // Constants
  bit [7:0] SLAVE_RESET_RESPONSE = 8'hB9;
  int slave_reset_response = SLAVE_RESET_RESPONSE;
  
  // Simple SPI slave model for testing
  logic [7:0] slave_rx_data = '0;
  logic [7:0] slave_tx_data = '0;
  logic [3:0] idle_counter = '0;
    
  clk_if m_clk_if();
  spi_if #(.CLK_DIV(CLK_DIV)) m_spi_if(m_clk_if.clk_tb);
  spi_slave_if slave_if(m_clk_if.clk_tb,SLAVE_RESET_RESPONSE);
  
  assign slave_if.slave_rx_data = slave_rx_data;

  spi #(.CLK_DIV(CLK_DIV)) dut (
    .clk(m_clk_if.clk_tb),
    .rst_n(m_spi_if.rst_n_tb),
    .start(m_spi_if.start_tb),
    .tx_data(m_spi_if.tx_data_tb),
    .rx_data(m_spi_if.rx_data_tb),
    .busy(m_spi_if.busy_tb),
    .done(m_spi_if.done_tb),
    .sclk(m_spi_if.sclk_tb),
    .mosi(m_spi_if.mosi_tb),
    .miso(m_spi_if.miso_tb),
    .cs_n(m_spi_if.cs_n_tb)
  );

  bind spi spi_assertions #(.NUM_BITS(8)) assertion_chk (
  .clk   (clk),
  .rst_n (rst_n),
  .start (start),
  .busy  (busy),
  .done  (done),
  .sclk  (sclk),
  .bit_cnt (bit_cnt),
  .rx_data (rx_data),
  .tx_data (tx_data),
  .cs_n (cs_n),
  .mosi (mosi),
  .miso (miso),
  .rx_reg (rx_reg),
  .tx_reg (tx_reg)
  );

  initial begin
      m_spi_if.rst_n_tb = '0;
      m_spi_if.start_tb = '0;
      m_spi_if.tx_data_tb = '0;
      m_spi_if.miso_tb = '0;
  end

  initial begin
    uvm_config_db#(virtual spi_if)::set(null, "*", "vif", m_spi_if);
    uvm_config_db#(virtual spi_if.drv_mp)::set(null, "*drv*", "vif", m_spi_if.drv_mp);
    uvm_config_db#(virtual spi_if.mon_mp)::set(null, "*mon*", "vif", m_spi_if.mon_mp);
    uvm_config_db#(virtual spi_slave_if.slv_mon_mp)::set(null, "*", "slave_vif", slave_if);


    fork
      begin
        //run_test("spi_base_test");
        run_test();// test will be chosen via UVM_TESTNAME
      end

      begin
        #1000000ns; // set timeout duration
        `uvm_fatal("TIMEOUT", $sformatf("Test timed out after %0t",$time))
      end
    join_any
    disable fork; // stop whichever thread is still running     
  end

  initial begin
    $fsdbDumpfile("dump.fsdb");
    $fsdbDumpSVA(0,spi_tb);
    $fsdbDumpvars(0, spi_tb);
  end


    
    always @(posedge m_spi_if.sclk_tb or negedge m_spi_if.rst_n_tb or posedge m_spi_if.cs_n_tb) begin
        if (!m_spi_if.rst_n_tb) begin
            slave_rx_data <= 8'h00;
            m_spi_if.miso_tb <= 1'b0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;
        end
	      else if (m_spi_if.cs_n_tb) begin
            m_spi_if.miso_tb <= 1'b0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;

	    `uvm_info("SLV-RLD", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                               slave_rx_data, slave_rx_data, slave_tx_data, slave_tx_data), UVM_MEDIUM)
        end
	      else begin
                // Shift in MOSI on rising edge
                slave_rx_data <= {slave_rx_data[6:0], m_spi_if.mosi_tb};

                // Update MISO immediately for next bit
                m_spi_if.miso_tb <= slave_tx_data[7];
                slave_tx_data <= {slave_tx_data[6:0], 1'b0};

		`uvm_info("SLV", $sformatf("RX_REG=0x%2h \(%8b\), TX_REG=0x%2h \(%8b\)",
                                           slave_rx_data, slave_rx_data, slave_tx_data, slave_tx_data), UVM_MEDIUM)
        end
    end

    always @(posedge m_spi_if.clk_tb or negedge m_spi_if.rst_n_tb) begin
        if (!m_spi_if.rst_n_tb) begin
            idle_counter <= 5'd0;
            slave_tx_data <= SLAVE_RESET_RESPONSE;
        end
        else if (m_spi_if.cs_n_tb) begin  // SPI idle (cs_n=1)
            if (idle_counter < 5'd7) begin
                slave_tx_data <= 8'h00;  // Drive 0 for 8 cycles
                idle_counter <= idle_counter + 1;
            end
            else begin
                slave_tx_data <= SLAVE_RESET_RESPONSE;  // Revert to default
            end
        end
        else begin  // SPI active (cs_n=0)
            idle_counter <= 5'd0;  // Reset counter
        end
    end


endmodule
