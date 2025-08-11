class high_prio_seq extends bus_seq;
  `uvm_object_utils(high_prio_seq)

  int min_delay;
  int max_delay;
  int delay;
  int seq_count;
  int seq_index;
  string seq_type;
  string seq_dir;

  bit [7:0] last_write_addr;

  function new(string name = "high_prio_seq");
    super.new(name);
    seq_index = 0;
    seq_type = "high";
  endfunction

  task body();
    bus_tran tr;
    `uvm_info(get_type_name(), "High Priority Sequence", UVM_MEDIUM)
    m_sequencer.lock(this);
    repeat (seq_count) begin
      seq_index++;
      // Write data to a random address
      req = bus_tran::type_id::create("req");
      start_item(req);
      assert(req.randomize() with { addr[7:4] == 4'hB; write == 1; });
      //assert(req.randomize() with { write == 1; });
      last_write_addr = req.addr;  // Store the write address directly
      seq_dir = "WR";
      `uvm_info(get_type_name(), $sformatf("Sent %s %0d/%0d %s seq: addr=0x%2h, data=0x%8h, write=%0b",
                                           seq_dir, seq_index, seq_count, seq_type, req.addr, req.data, req.write),
					   UVM_MEDIUM)
      req.seq_count = this.seq_count;
      req.seq_index = this.seq_index;
      req.seq_type = this.seq_type;
      req.seq_dir = this.seq_dir;
      finish_item(req);
      // Read the data back from the write adddress
      req = bus_tran::type_id::create("req");
      start_item(req);
      req.addr = last_write_addr;
      req.write = 0;
      seq_dir = "RD";
      `uvm_info(get_type_name(), $sformatf("Sent %s %0d/%0d %s seq: addr=0x%2h, data=0x%8h, write=%0b Next seq after %0d",
                                           seq_dir, seq_index, seq_count, seq_type, req.addr, req.data, req.write, delay),
                                           UVM_MEDIUM)
      req.seq_count = this.seq_count;
      req.seq_index = this.seq_index;
      req.seq_type = this.seq_type;
      req.seq_dir = this.seq_dir;
      finish_item(req);
    end
    m_sequencer.unlock(this);
  endtask
endclass


class low_prio_seq extends bus_seq;
  `uvm_object_utils(low_prio_seq)

  int min_delay;
  int max_delay;
  int delay;
  int seq_count;
  int seq_index;
  string seq_type;
  string seq_dir;

  bit [7:0] last_write_addr;

  function new(string name = "low_prio_seq");
    super.new(name);
    seq_index = 0;
    seq_type = "low";
  endfunction

  task body();
    bus_tran tr;
    `uvm_info(get_type_name(), "Low Priority Sequence", UVM_MEDIUM)
    repeat (seq_count) begin
      seq_index++;
      // Write data to a random address
      req = bus_tran::type_id::create("req");
      start_item(req);
      assert(req.randomize() with { addr[7:4] == 4'hF; write == 1; });
      //assert(req.randomize() with { write == 1; });
      last_write_addr = req.addr;  // Store the write address directly
      seq_dir = "WR";
      `uvm_info(get_type_name(), $sformatf("Sent %s %0d/%0d %s seq: addr=0x%2h, data=0x%8h, write=%0b",
                                           seq_dir, seq_index, seq_count, seq_type, req.addr, req.data, req.write),
					   UVM_MEDIUM)
      req.seq_count = this.seq_count;
      req.seq_index = this.seq_index;
      req.seq_type = this.seq_type;
      req.seq_dir = this.seq_dir;
      finish_item(req);
      // Read the data back from the write adddress
      req = bus_tran::type_id::create("req");
      start_item(req);
      req.addr = last_write_addr;
      req.write = 0;
      seq_dir = "RD";
      `uvm_info(get_type_name(), $sformatf("Sent %s %0d/%0d %s seq: addr=0x%2h, data=0x%8h, write=%0b Next seq after %0d",
                                           seq_dir, seq_index, seq_count, seq_type, req.addr, req.data, req.write, delay),
                                           UVM_MEDIUM)
      req.seq_count = this.seq_count;
      req.seq_index = this.seq_index;
      req.seq_type = this.seq_type;
      req.seq_dir = this.seq_dir;
      finish_item(req);
    end
  endtask
endclass

