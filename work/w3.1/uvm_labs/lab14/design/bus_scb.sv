class bus_scb extends uvm_scoreboard;
  `uvm_component_utils(bus_scb)
    
  // Use implementation port to receive transactions
  uvm_analysis_imp #(bus_tran, bus_scb) mon_imp;
    
  int passed_count = 0;
  int failed_count = 0;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mon_imp = new("mon_imp", this);
  endfunction
    
  // This will be called when transactions arrive
  function void write(bus_tran tr);
    // Add in assertion for demo purpose
    assert(tr.write == 1 && tr.addr[7:4] == 4'hA) else begin
      `uvm_error("ASSERTION", $sformatf("FAIL %0d/%0d %s transaction: addr=0x%2h, data=0x%8h, write=%0b ++++++++++++++++",
                                         tr.seq_index, tr.seq_count, tr.seq_type, tr.addr, tr.data, tr.write))
    end

    if (tr.write == 1 && tr.addr[7:4] == 4'hA) begin
      passed_count++;
      `uvm_info("SCOREBOARD", $sformatf("PASS %0d/%0d %s transaction: addr=0x%2h, data=0x%8h, write=%0b",
                                        tr.seq_index, tr.seq_count, tr.seq_type, tr.addr, tr.data, tr.write), UVM_MEDIUM)
    end else begin
      failed_count++;
      `uvm_error("SCOREBOARD", $sformatf("FAIL %0d/%0d %s transaction: addr=0x%2h, data=0x%8h, write=%0b ================",
                                         tr.seq_index, tr.seq_count, tr.seq_type, tr.addr, tr.data, tr.write))
    end
  endfunction
    
  function void report_phase(uvm_phase phase);
    `uvm_info("SCOREBOARD", $sformatf("Test Results: Passed=%0d Failed=%0d",
	                                  passed_count, failed_count), UVM_NONE)
  endfunction
endclass
