class bus_scb extends uvm_scoreboard;
  `uvm_component_utils(bus_scb)

  // Use implementation port to receive transactions
  uvm_analysis_imp #(bus_tran, bus_scb) scb_imp;

  int passed_count = 0;
  int failed_count = 0;
  int passed_wr_count = 0;
  int passed_rd_count = 0;
  int failed_wr_res_count = 0;
  int failed_rd_res_count = 0;
  int tran_count;
  int tran_index;
  string tran_dir;
  string tran_type;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    scb_imp = new("scb_imp", this);
  endfunction

  function void write(bus_tran tr_dut);
    if (tr_dut.addr[7:4] == 4'hA) begin
      passed_count++;
      if (tr_dut.write == 1) passed_wr_count++;
      if (tr_dut.write == 0) passed_rd_count++;
      `uvm_info("SCOREBOARD", $sformatf("PASS %s %0d/%0d %s tran: addr=0x%2h, data=0x%8h, write=%0b, control reg 0xA0-0xAF",
                                        tr_dut.tran_dir, tr_dut.tran_index, tr_dut.tran_count,
                                        tr_dut.tran_type, tr_dut.addr, tr_dut.data, tr_dut.write),
                                        UVM_MEDIUM)
    end else if (tr_dut.addr[7:4] == 4'hB) begin
      passed_count++;
      if (tr_dut.write == 1) passed_wr_count++;
      if (tr_dut.write == 0) passed_rd_count++;
      `uvm_info("SCOREBOARD", $sformatf("PASS %s %0d/%0d %s tran: addr=0x%2h, data=0x%8h, write=%0b, status reg 0xB0-0xBF",
                                        tr_dut.tran_dir, tr_dut.tran_index, tr_dut.tran_count,
                                        tr_dut.tran_type, tr_dut.addr, tr_dut.data, tr_dut.write), UVM_MEDIUM)
    end else if (tr_dut.addr[7:4] == 4'hF) begin
      failed_count++;
      if (tr_dut.write == 1) failed_wr_res_count++;
      if (tr_dut.write == 0) failed_rd_res_count++;
      `uvm_error("SCOREBOARD", $sformatf("FAIL %s %0d/%0d %s tran: addr=0x%2h, data=0x%8h, write=%0b, reserved 0xF0-0xFF",
                                         tr_dut.tran_dir, tr_dut.tran_index, tr_dut.tran_count,
                                         tr_dut.tran_type, tr_dut.addr, tr_dut.data, tr_dut.write))
    end else begin
      passed_count++;
      if (tr_dut.write == 1) passed_wr_count++;
      if (tr_dut.write == 0) passed_rd_count++;
      `uvm_info("SCOREBOARD", $sformatf("PASS %s %0d/%0d %s tran: addr=0x%2h, data=0x%8h, write=%0b",
                                        tr_dut.tran_dir, tr_dut.tran_index, tr_dut.tran_count,
                                        tr_dut.tran_type, tr_dut.addr, tr_dut.data, tr_dut.write), UVM_MEDIUM)
    end
  endfunction

  real pass_rate;
  real fail_rate;
  bit test_passed;
  string test_summary;

  function void extract_phase(uvm_phase phase);
    // Calculate derived metrics
    int total_transactions = passed_count + failed_count;

    if (total_transactions > 0) begin
      // real' is a casting syntax, creates a temporary real (floating-point) version of the value
      // ' is called the cast operator
      pass_rate = (real'(passed_count) / real'(total_transactions)) * 100;
      fail_rate = (real'(failed_count) / real'(total_transactions)) * 100;
    end else begin
      pass_rate = 0;
      fail_rate = 0;
    end

    // Determine overall test status
    test_passed = (failed_count == 0);  // If failed_count is 0, return true or 1, meaning test_passed is true or 1
    test_summary = test_passed ? "TEST PASSED" : "TEST FAILED";
  endfunction

  function void check_phase(uvm_phase phase);
    // Final verification of test results
    if (failed_count > 0) begin
        `uvm_error("CHECK", $sformatf("Scoreboard detected %0d failures", failed_count))
    end

    // Additional checks could be added here, for example:
    // - Minimum transaction count requirements
    // - Specific pattern requirements
    // - Protocol violation checks
  endfunction

  function void report_phase(uvm_phase phase);
    `uvm_info("SCOREBOARD", test_summary, UVM_NONE)
    `uvm_info("SCOREBOARD", $sformatf("Pass Rate: %.2f%%", pass_rate), UVM_NONE)

    `uvm_info("SCOREBOARD", $sformatf("Passed Tran: Passed=%0d Passed(WR)=%0d Passed(RD)=%0d",
                                      passed_count, passed_wr_count, passed_rd_count), UVM_NONE)
    `uvm_info("SCOREBOARD", $sformatf("Failed Tran: Failed=%0d Failed(WR_RES)=%0d Failed(RD_RES)=%0d",
                                      failed_count, failed_wr_res_count, failed_rd_res_count), UVM_NONE)
  endfunction
endclass

