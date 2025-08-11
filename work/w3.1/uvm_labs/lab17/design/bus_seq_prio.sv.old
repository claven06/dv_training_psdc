class high_prio_seq extends bus_seq;
  `uvm_object_utils(high_prio_seq)

  int seq_count;
  int seq_index;
  string seq_type;

  function new(string name = "high_prio_seq");
    super.new(name);
    seq_index = 0;
    seq_type = "high";
  endfunction

  task body();
    bus_tran req;
    `uvm_info(get_type_name(), "High Priority Sequence", UVM_MEDIUM)

    m_sequencer.lock(this);

    repeat (seq_count) begin
      req = bus_tran::type_id::create("req");
      start_item(req);
      assert(req.randomize() with { addr[7:4] == 4'hF; write == 0; });
      delay = get_random_delay();
      seq_index++;
      req.seq_count = this.seq_count;
      req.seq_index = this.seq_index;
      req.seq_type = this.seq_type;
      `uvm_info(get_type_name(), $sformatf("Sent %0d/%0d %s sequences: addr=0x%2h, data=0x%8h, write=%0b Next sequence after %0d",
                                           seq_index, seq_count, seq_type, req.addr, req.data, req.write, delay),
                                           UVM_MEDIUM)
      #delay;
      finish_item(req);
    end

    m_sequencer.unlock(this);

  endtask
endclass

class low_prio_seq extends bus_seq;
  `uvm_object_utils(low_prio_seq)

  int seq_count;
  int seq_index;
  string seq_type;

  function new(string name = "low_prio_seq");
    super.new(name);
    seq_index = 0;
    seq_type = "low";
  endfunction

  task body();
    bus_tran req;
    `uvm_info(get_type_name(), "Low Priority Sequence", UVM_MEDIUM)

    repeat (seq_count) begin
      req = bus_tran::type_id::create("req");
      start_item(req);
      assert(req.randomize() with { addr[7:4] == 4'hE; write == 0; });
      delay = get_random_delay();
      seq_index++;
      req.seq_count = this.seq_count;
      req.seq_index = this.seq_index;
      req.seq_type = this.seq_type;
      `uvm_info(get_type_name(), $sformatf("Sent %0d/%0d %s sequences: addr=0x%2h, data=0x%8h, write=%0b Next sequence after %0d",
                                           seq_index, seq_count, seq_type, req.addr, req.data, req.write, delay),
                                           UVM_MEDIUM)
      #delay;
      finish_item(req);
    end
  endtask
endclass
