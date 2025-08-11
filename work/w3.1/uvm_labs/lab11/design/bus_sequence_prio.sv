class high_prio_seq extends bus_sequence;
    `uvm_object_utils(high_prio_seq)
    int delay;
    int sent_count;

    function new(string name = "high_prio_seq");
        super.new(name);
        sent_count = 0;
    endfunction

    task body();
      bus_transaction req;
      `uvm_info(get_type_name(), "High Priority Sequence", UVM_MEDIUM)
      m_sequencer.lock(this);
      repeat (seq_count) begin
         req = bus_transaction::type_id::create("req");
         start_item(req);
         assert(req.randomize() with { addr[7:4] == 4'hF; write == 0; }); // Limit to write transactions only
         req.seq_type = "high";  // Lab 11
         delay = get_random_delay();  // Lab 11
         sent_count++;  // Lab 11
         `uvm_info(get_type_name(), $sformatf("Sent %0d/%0d %s sequences, next sequence after %0d", sent_count, seq_count, req.seq_type, delay), UVM_MEDIUM)  // Lab 11
         #delay;  // Lab 11
        finish_item(req);
      end
      m_sequencer.unlock(this);
    endtask
endclass

class low_prio_seq extends bus_sequence;
    `uvm_object_utils(low_prio_seq)

    function new(string name = "low_prio_seq");
        super.new(name);
    endfunction

    task body();
      bus_transaction req;
      `uvm_info(get_type_name(), "Low Priority Sequence", UVM_MEDIUM)
      repeat (seq_count) begin
         req = bus_transaction::type_id::create("req");
         start_item(req);
         assert(req.randomize() with { addr[7:4] == 4'hE; write == 0; }); // Limit to write transactions only
         req.seq_type = "low";  // Lab 11
         delay = get_random_delay();  // Lab 11
         sent_count++;  // Lab 11
         `uvm_info(get_type_name(), $sformatf("Sent %0d/%0d %s sequences, next sequence after %0d", sent_count, seq_count, req.seq_type, delay), UVM_MEDIUM)  // Lab 11
         #delay;  // Lab 11
         finish_item(req);
      end
    endtask
endclass
