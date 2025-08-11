class fa_scb extends uvm_scoreboard;
  `uvm_component_utils(fa_scb)

  // Use implementation port to receive transactions
  uvm_analysis_imp #(fa_tran, fa_scb) scb_imp;

  int passed_count = 0;
  int failed_count = 0;
  int tran_count;
  int tran_index;
  string tran_type;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    tran_index = 1;
    scb_imp = new("scb_imp", this);
  endfunction

  function void write(fa_tran tr_dut);
    bit exp_sum = tr_dut.a ^ tr_dut.b ^ tr_dut.cin;
    //bit exp_cout = (tr_dut.a & tr_dut.b) & (tr_dut.cin & (tr_dut.a ^ tr_dut.b));
    bit exp_cout = (tr_dut.a & tr_dut.b) | (tr_dut.cin & (tr_dut.a ^ tr_dut.b));

    if(tr_dut.sum == exp_sum && tr_dut.cout == exp_cout) begin
      passed_count++;
      `uvm_info("SCOREBOARD", $sformatf("PASS %0d/%0d %s tran: a_tb=%b, b_tb=%b, cin_tb=%b > sum_tb=%b cout_tb=%b",
                                        tran_index, tr_dut.tran_count, tr_dut.tran_type, tr_dut.a, tr_dut.b, tr_dut.cin, tr_dut.sum, tr_dut.cout),
				       	UVM_MEDIUM)
    end
    else if(tr_dut.sum != exp_sum) begin
      failed_count++;
      `uvm_error("SCOREBOARD", $sformatf("FAIL SUM %0d/%0d %s tran: a_tb=%b, b_tb=%b, cin_tb=%b > sum_tb=%b (exp %b) <<<<<<<<<<<<<<<<",
                                         tran_index, tr_dut.tran_count, tr_dut.tran_type, tr_dut.a, tr_dut.b, tr_dut.cin, tr_dut.sum, exp_sum))
    end
    else if(tr_dut.cout != exp_cout) begin
      failed_count++;
      `uvm_error("SCOREBOARD", $sformatf("FAIL COUT %0d/%0d %s tran: a_tb=%b, b_tb=%b, cin_tb=%b > cout_tb=%b (exp %b) <<<<<<<<<<<<<<<<",
                                         tran_index, tr_dut.tran_count, tr_dut.tran_type, tr_dut.a, tr_dut.b, tr_dut.cin, tr_dut.cout, exp_cout))
    end
    tran_index++;
  endfunction

  function void report_phase(uvm_phase phase);
    `uvm_info("SCOREBOARD", $sformatf("Test Complete. Passed: %0d Failed: %0d", passed_count, failed_count), UVM_NONE)
  endfunction
endclass

