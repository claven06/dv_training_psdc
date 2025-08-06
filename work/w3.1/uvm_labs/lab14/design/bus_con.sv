class bus_con extends uvm_component;
  `uvm_component_utils(bus_con)

  // Analysis implementation port for receiving transactions
  uvm_analysis_imp #(bus_tran, bus_con) con_imp;
   
  // TLM FIFO for storing transactions
  uvm_tlm_fifo #(bus_tran) data_fifo;
   
  // Processing delay time setting
  local int fifo_process_time = 13;
   
  // Counters and metrics
  int num_received = 0;
  int num_processed = 0;
  int num_errors = 0;
  int fifo_size = 4;  // Set your desired FIFO size
  int fifo_overflows = 0;
  int fifo_max_utilization = 0;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // Create FIFO
    data_fifo = new("data_fifo", this, fifo_size);
    con_imp = new("con_imp", this);

    `uvm_info("FIFO_INFO", $sformatf("FIFO Size: %0d", fifo_size), UVM_MEDIUM)
    `uvm_info("FIFO_INFO", $sformatf("FIFO Process Time: %0d", fifo_process_time), UVM_MEDIUM)
  endfunction

  // Analysis port write implementation
  function void write(bus_tran tr);
    num_received++;
    update_fifo_stats();

    // Try to put into FIFO
    if (!data_fifo.try_put(tr)) begin
      fifo_overflows++;
      `uvm_error("FIFO_OVERFLOW",
                 $sformatf("FIFO overflow! Discarding %0d/%0d %s transaction: addr=0x%2h, data=0x%8h, write=%0b >>>>>>>>>>>>>>>>",
                 tr.seq_index, tr.seq_count, tr.seq_type, tr.addr, tr.data, tr.write))
    end
    else begin
      `uvm_info("FIFO_ADD",
                $sformatf("Added %0d/%0d %s transaction to FIFO (size=%0d): addr=0x%2h, data=0x%8h, write=%0b",
                          tr.seq_index, tr.seq_count, tr.seq_type, data_fifo.used(), tr.addr, tr.data, tr.write), UVM_MEDIUM)
    end
  endfunction

  // Main processing task
  virtual task run_phase(uvm_phase phase);
    bus_tran tr;
    forever begin
      // Simulate processing delay
      #fifo_process_time;

      // Blocking get from FIFO
      data_fifo.get(tr);
      num_processed++;
         
      `uvm_info("FIFO_PROCESS",
                $sformatf("Processing %0d/%0d %s transaction (remaining=%0d): addr=0x%2h, data=0x%8h, write=%0b",
                          tr.seq_index, tr.seq_count, tr.seq_type, data_fifo.used(), tr.addr, tr.data, tr.write), UVM_MEDIUM)
         
      // Transaction validation check
      if (tr.write == 0) begin
        num_errors++;
        `uvm_error("CONSUMER_CHECK",
                   $sformatf("Invalid %0d/%0d %s transaction! addr=0x%2h, data=0x%8h, write=%0b <<<<<<<<<<<<<<<<",
                   tr.seq_index, tr.seq_count, tr.seq_type, tr.addr, tr.data, tr.write))
      end
    end
  endtask

  // Helper function to update FIFO statistics
  function void update_fifo_stats();
    int current_used = data_fifo.used();
    if (current_used + 1 >= fifo_max_utilization) begin
      fifo_max_utilization = current_used + 1;
    end
  endfunction

  // Report phase for summary
  function void report_phase(uvm_phase phase);
    `uvm_info("CONSUMER_REPORT",
              $sformatf("Total received transactions: %0d", num_received),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("Total processed transactions: %0d", num_processed),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("Total errors detected: %0d", num_errors),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("FIFO overflows: %0d", fifo_overflows),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("Maximum FIFO utilization: %0d/%0d", fifo_max_utilization, fifo_size),
              UVM_NONE)
  endfunction
endclass
