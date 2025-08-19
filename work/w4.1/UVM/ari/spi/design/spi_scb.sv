class spi_scb extends uvm_scoreboard;
  `uvm_component_utils(spi_scb)
  
  // Use implementation port to receive transactions
  uvm_analysis_imp #(spi_tran, spi_scb) scb_imp;
  
  int passed_count = 0;
  int failed_count = 0;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    scb_imp = new("scb_imp", this);
  endfunction


  function void write(spi_tran tr_dut);

    if (!tr_dut.rst_n) begin
      if ((tr_dut.sclk === 1'b0) && (tr_dut.busy === 1'b0) && (tr_dut.done === 1'b0) && (tr_dut.cs_n === 1'b1) && (tr_dut.rx_data === 8'h00)) begin
        `uvm_info("SCOREBOARD", $sformatf("PASS RESET CHECK: When rst_n=%b, all outputs init to '0 except cs_n", tr_dut.rst_n),UVM_MEDIUM)
      end
      else begin
        `uvm_error("SCOREBOARD", $sformatf("FAIL RESET CHECK: When rst_n=%b, the outputs are not in init state", tr_dut.rst_n))
      end
    end
    else if(tr_dut.done) begin
      if (tr_dut.done && (tr_dut.slave_rx_data === tr_dut.tx_data) && (tr_dut.slave_tx_data === tr_dut.rx_data)) begin
        passed_count++;
        `uvm_info("SCOREBOARD", $sformatf("PASS tran: When done_tb=%b, slave_rx_data(%b) == tx_data(%b) && slave_tx_data(%b) == rx_data(%b)", tr_dut.done, tr_dut.slave_rx_data, tr_dut.tx_data, tr_dut.slave_tx_data, tr_dut.rx_data),UVM_MEDIUM)
      end
      else begin
        failed_count++;
        `uvm_error("SCOREBOARD", $sformatf("FAIL tran: done_tb=%b, MISMATCH: !((slave_rx_data === tx_data) && (slave_tx_data === rx_data)), Current values: slave_rx_data=%b, tx_data=%b, slave_tx_data=%b, rx_data=%b", tr_dut.done, tr_dut.slave_rx_data, tr_dut.tx_data, tr_dut.slave_tx_data, tr_dut.rx_data))
      end    
    end

  endfunction

  function void report_phase(uvm_phase phase);
    `uvm_info("SCOREBOARD", $sformatf("Test Complete. Passed: %0d Failed: %0d", passed_count, failed_count), UVM_NONE)
  endfunction
endclass