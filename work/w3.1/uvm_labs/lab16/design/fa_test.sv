class fa_test extends uvm_test;
  `uvm_component_utils(fa_test)

  fa_env env;
  fa_seq seq;

  int seq_count = 10;
  int seq_min_delay = 0,  seq_max_delay = 0;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = fa_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    seq = fa_seq::type_id::create("seq");

    seq.seq_count = this.seq_count;
    seq.min_delay = this.seq_min_delay;
    seq.max_delay = this.seq_max_delay;

    `uvm_info("TEST", $sformatf("Starting sequences with config:\n\
                                Normal: count=%0d, delay=%0d-%0d",
                                seq.seq_count, seq.min_delay, seq.max_delay),
                                UVM_MEDIUM)

    phase.raise_objection(this);
    fork
      seq.start(env.agt.sqr);
    join
    wait(env.scb.tran_index == seq.seq_count);
    //wait(env.con.num_processed + env.con.fifo_overflows == env.con.num_received);
    phase.drop_objection(this);
  endtask
endclass
