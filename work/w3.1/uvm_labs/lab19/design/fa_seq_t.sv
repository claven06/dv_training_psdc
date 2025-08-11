class fa_seq_t extends uvm_sequence #(fa_tran);
  `uvm_object_utils(fa_seq_t)

  int min_delay;
  int max_delay;
  int delay;
  int seq_count;
  int seq_index;
  string seq_type;
  bit [2:0] bits;

  function new(string name = "fa_seq");
    super.new(name);
    seq_index = 0;
  endfunction

  function int get_random_delay();
    return $urandom_range(min_delay, max_delay);
  endfunction

  task body();
    fa_tran tr;
    `uvm_info(get_type_name(), $sformatf("Sequence: %s", seq_type), UVM_MEDIUM)
    for (seq_index = 1; seq_index <= seq_count; seq_index++) begin
      tr = fa_tran::type_id::create("tr");
      bits = seq_index - 1;
      start_item(tr);
      tr.a = bits[2]; tr.b = bits[1]; tr.cin = bits[0];
      assert(tr.a inside {0,1} && tr.b inside {0,1} && tr.cin inside {0,1})
      delay = get_random_delay();
      tr.seq_count = this.seq_count;
      tr.seq_index = this.seq_index;
      tr.seq_type = this.seq_type;
      #delay;
      finish_item(tr);
      `uvm_info(get_type_name(), $sformatf("Sent %0d/%0d %s sequences: a=%0b, b=%0b, cin=%0b Next sequence after %0d",
                                           seq_index, seq_count, seq_type, tr.a, tr.b, tr.cin, delay),
                                           UVM_MEDIUM)
    end
  endtask
endclass
