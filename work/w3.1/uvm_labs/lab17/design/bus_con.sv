class bus_con extends uvm_component;
  `uvm_component_utils(bus_con)

  // Analysis implementation port for receiving transactions
  uvm_analysis_imp #(bus_tran, bus_con) con_imp;

  // TLM FIFO for storing transactions
  uvm_tlm_fifo #(bus_tran) wr_data_fifo;
  uvm_tlm_fifo #(bus_tran) rd_data_fifo;

  // Processing delay time setting
  local int wr_fifo_process_time = 60;
  local int rd_fifo_process_time = 59;

  // Counters and metrics
  int wr_num_received = 0;
  int wr_num_processed = 0;
  int rd_num_received = 0;
  int rd_num_processed = 0;
  //int num_errors = 0;
  int wr_num_pass = 0;
  int rd_num_pass = 0;
  int wr_num_fail = 0;
  int rd_num_fail = 0;
  int wr_fifo_size = 10;  // Set your desired FIFO size
  int rd_fifo_size = 9;  // Set your desired FIFO size
  int wr_fifo_overflows = 0;
  int rd_fifo_overflows = 0;
  int wr_fifo_max_utilization = 0;
  int rd_fifo_max_utilization = 0;

  int tran_count;
  int tran_index;
  string tran_type;
  string tran_dir;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    con_imp = new("con_imp", this);

    // Create FIFO
    wr_data_fifo = new("wr_data_fifo", this, wr_fifo_size);
    `uvm_info("FIFO_INFO", $sformatf("WR FIFO Size: %0d", wr_fifo_size), UVM_MEDIUM)
    `uvm_info("FIFO_INFO", $sformatf("WR FIFO Process Time: %0d", wr_fifo_process_time), UVM_MEDIUM)
    rd_data_fifo = new("rd_data_fifo", this, rd_fifo_size);
    `uvm_info("FIFO_INFO", $sformatf("RD FIFO Size: %0d", rd_fifo_size), UVM_MEDIUM)
    `uvm_info("FIFO_INFO", $sformatf("RD FIFO Process Time: %0d", rd_fifo_process_time), UVM_MEDIUM)
  endfunction

  // Analysis port write implementation
  function void write(bus_tran tr_dut);
    if (tr_dut.write == 1) begin
      wr_num_received++;
      wr_fifo_max_utilization = update_fifo_stats(wr_data_fifo, wr_fifo_max_utilization, "wr_data_fifo");

      // Try to put into FIFO: WR
      if (!wr_data_fifo.try_put(tr_dut)) begin
        wr_fifo_overflows++;
        `uvm_error("FIFO_OVERFLOW",
                   $sformatf("%s: Discard %0d/%0d %s tran: addr=0x%2h, data=0x%8h, write=%0b >>>>>>>>>>>>>>>>",
                             tr_dut.tran_dir, tr_dut.tran_index, tr_dut.tran_count,
                             tr_dut.tran_type, tr_dut.addr, tr_dut.data, tr_dut.write))
      end else begin
        `uvm_info("FIFO_ADD",
                  $sformatf("%s: %0d/%0d %s tran (size=%0d): addr=0x%2h, data=0x%8h, write=%0b",
                            tr_dut.tran_dir, tr_dut.tran_index, tr_dut.tran_count,
                            tr_dut.tran_type, wr_data_fifo.used(), tr_dut.addr,
                            tr_dut.data, tr_dut.write), UVM_MEDIUM)
      end
    end else begin
      rd_num_received++;
      rd_fifo_max_utilization = update_fifo_stats(rd_data_fifo, rd_fifo_max_utilization, "rd_data_fifo");

      // Try to put into FIFO: WR
      if (!rd_data_fifo.try_put(tr_dut)) begin
        rd_fifo_overflows++;
        `uvm_error("FIFO_OVERFLOW",
                   $sformatf("%s: Discard %0d/%0d %s tran: addr=0x%2h, data=0x%8h, write=%0b >>>>>>>>>>>>>>>>",
                             tr_dut.tran_dir, tr_dut.tran_index, tr_dut.tran_count,
                             tr_dut.tran_type, tr_dut.addr, tr_dut.data, tr_dut.write))
      end else begin
        `uvm_info("FIFO_ADD",
                  $sformatf("%s: %0d/%0d %s tran (size=%0d): addr=0x%2h, data=0x%8h, write=%0b",
                            tr_dut.tran_dir, tr_dut.tran_index, tr_dut.tran_count,
                            tr_dut.tran_type, rd_data_fifo.used(), tr_dut.addr,
                            tr_dut.data, tr_dut.write), UVM_MEDIUM)
      end
    end
  endfunction

  // Main processing task
  virtual task run_phase(uvm_phase phase);
    bus_tran tr_dut_wr, tr_dut_rd;
    bit [31:0] last_read_data;
    forever begin
      fork
        begin
          wr_data_fifo.get(tr_dut_wr);
          #wr_fifo_process_time;
          wr_num_processed++;
          `uvm_info("FIFO_PROCESS",
                    $sformatf("%s: %0d/%0d %s tran (remaining=%0d): addr=0x%2h, data=0x%8h, write=%0b",
                              tr_dut_wr.tran_dir, tr_dut_wr.tran_index, tr_dut_wr.tran_count,
                              tr_dut_wr.tran_type, wr_data_fifo.used(), tr_dut_wr.addr,
                              tr_dut_wr.data, tr_dut_wr.write), UVM_MEDIUM)
        end
        begin
          rd_data_fifo.get(tr_dut_rd);
          #rd_fifo_process_time;
          rd_num_processed++;
          `uvm_info("FIFO_PROCESS",
                    $sformatf("%s: %0d/%0d %s tran (remaining=%0d): addr=0x%2h, data=0x%8h, write=%0b",
                              tr_dut_rd.tran_dir, tr_dut_rd.tran_index, tr_dut_rd.tran_count,
                              tr_dut_rd.tran_type, rd_data_fifo.used(), tr_dut_rd.addr,
                              tr_dut_rd.data, tr_dut_rd.write), UVM_MEDIUM)

          if (tr_dut_rd.addr[7:4] == 4'hA) begin
            if (tr_dut_rd.data == tr_dut_wr.data) begin
              rd_num_pass++;
              `uvm_info("FIFO_VAL",
                        $sformatf("PASS %s: %0d/%0d %s tran addr=0x%2h, data=0x%8h (rdata==wdata, control reg 0xA0-0xAF)",
                                  tr_dut_rd.tran_dir, tr_dut_rd.tran_index, tr_dut_rd.tran_count,
                                  tr_dut_rd.tran_type, tr_dut_rd.addr, tr_dut_rd.data), UVM_MEDIUM)
            end else begin
              rd_num_fail++;
              `uvm_error("FIFO_VAL",
                         $sformatf("FAIL %s: %0d/%0d %s tran addr=0x%2h, data=0x%8h (rdata!=wdata, control reg 0xA0-0xAF)",
                                   tr_dut_rd.tran_dir, tr_dut_rd.tran_index, tr_dut_rd.tran_count,
                                   tr_dut_rd.tran_type, tr_dut_rd.addr, tr_dut_rd.data))
            end
          end
          else if (tr_dut_rd.addr[7:4] == 4'hB) begin
            if (tr_dut_rd.addr[7:0] == tr_dut_rd.data[7:0]) begin
              rd_num_pass++;
              `uvm_info("FIFO_VAL",
                        $sformatf("PASS %s: %0d/%0d %s tran addr=0x%2h, data=0x%8h (rdata==waddr, status reg 0xA0-0xAF)",
                                  tr_dut_rd.tran_dir, tr_dut_rd.tran_index, tr_dut_rd.tran_count,
                                  tr_dut_rd.tran_type, tr_dut_rd.addr, tr_dut_rd.data), UVM_MEDIUM)
            end else begin
              rd_num_fail++;
              `uvm_error("FIFO_VAL",
                         $sformatf("FAIL %s: %0d/%0d %s tran addr=0x%2h, data=0x%8h (rdata!=waddr, status reg 0xA0-0xAF)",
                                   tr_dut_rd.tran_dir, tr_dut_rd.tran_index, tr_dut_rd.tran_count,
                                   tr_dut_rd.tran_type, tr_dut_rd.addr, tr_dut_rd.data))
            end
          end
          else if (tr_dut_rd.addr[7:4] == 4'hF) begin
            if (tr_dut_rd.data == last_read_data) begin
              rd_num_pass++;
              `uvm_info("FIFO_VAL",
                        $sformatf("PASS %s: %0d/%0d %s tran addr=0x%2h, data=0x%8h (rdata==last_rdata, reserved 0xF0-0xFF, wdata 0x%8h dropped)",
                                  tr_dut_rd.tran_dir, tr_dut_rd.tran_index, tr_dut_rd.tran_count,
                                  tr_dut_rd.tran_type, tr_dut_rd.addr, tr_dut_rd.data, tr_dut_wr.data), UVM_MEDIUM)
            end else begin
              rd_num_fail++;
              `uvm_error("FIFO_VAL",
                         $sformatf("FAIL %s: %0d/%0d %s tran addr=0x%2h, data=0x%8h (rdata!=last_rdata, reserved 0xF0-0xFF, wdata 0x%8h dropped)",
                                   tr_dut_rd.tran_dir, tr_dut_rd.tran_index, tr_dut_rd.tran_count,
                                   tr_dut_rd.tran_type, tr_dut_rd.addr, tr_dut_rd.data, tr_dut_wr.data))
            end
          end
          else begin
            if (tr_dut_rd.data == tr_dut_wr.data) begin
              rd_num_pass++;
              `uvm_info("FIFO_VAL",
                        $sformatf("PASS %s: %0d/%0d %s tran addr=0x%2h, data=0x%8h (rdata==wdata 0x%8h)",
                                  tr_dut_rd.tran_dir, tr_dut_rd.tran_index, tr_dut_rd.tran_count,
                                  tr_dut_rd.tran_type, tr_dut_rd.addr, tr_dut_rd.data, tr_dut_wr.data), UVM_MEDIUM)
            end else begin
              rd_num_fail++;
              `uvm_error("FIFO_VAL",
                         $sformatf("FAIL %s: %0d/%0d %s tran addr=0x%2h, data=0x%8h (rdata!=wdata 0x%8h)",
                                   tr_dut_rd.tran_dir, tr_dut_rd.tran_index, tr_dut_rd.tran_count,
                                   tr_dut_rd.tran_type, tr_dut_rd.addr, tr_dut_rd.data, tr_dut_wr.data))
            end
          end
          last_read_data = tr_dut_rd.data;
        end
      join
    end
  endtask

  // Helper function to update FIFO statistics
  function int update_fifo_stats(
        uvm_tlm_fifo #(bus_tran) fifo,
        int fifo_max_utilization,
        string fifo_name
  );
    int current_used = fifo.used();
    if (current_used + 1 >= fifo_max_utilization) begin
      fifo_max_utilization = current_used + 1;
    end
    return fifo_max_utilization;
  endfunction

  // Report phase for summary
  function void report_phase(uvm_phase phase);
    `uvm_info("CONSUMER_REPORT",
              $sformatf("Total WR received transactions: %0d", wr_num_received),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("Total WR processed transactions: %0d", wr_num_processed),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("WR FIFO overflows: %0d", wr_fifo_overflows),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("Maximum WR FIFO utilization: %0d/%0d", wr_fifo_max_utilization, wr_fifo_size),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("Total RD received transactions: %0d", rd_num_received),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("Total RD processed transactions: %0d", rd_num_processed),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("Total RD pass detected: %0d", rd_num_pass),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("Total RD fail detected: %0d", rd_num_fail),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("RD FIFO overflows: %0d", rd_fifo_overflows),
              UVM_NONE)
    `uvm_info("CONSUMER_REPORT",
              $sformatf("Maximum RD FIFO utilization: %0d/%0d", rd_fifo_max_utilization, rd_fifo_size),
              UVM_NONE)
  endfunction
endclass
