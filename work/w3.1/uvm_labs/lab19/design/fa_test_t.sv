class fa_test_t extends uvm_test;
  `uvm_component_utils(fa_test_t)

  fa_env env;
  fa_seq_t seq_t;

  string seq_type = "target";
  int seq_count = 8;
  int seq_min_delay = 0,  seq_max_delay = 0;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = fa_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    seq_t = fa_seq_t::type_id::create("seq_t");
    seq_t.seq_type = this.seq_type;
    seq_t.seq_count = this.seq_count;
    seq_t.min_delay = this.seq_min_delay;
    seq_t.max_delay = this.seq_max_delay;

    `uvm_info("TEST", $sformatf("Starting %s sequences with config: count=%0d, delay=%0d-%0d",
                                seq_t.seq_type, seq_t.seq_count, seq_t.min_delay, seq_t.max_delay),
                                UVM_MEDIUM)


    phase.raise_objection(this);
    fork
      seq_t.start(env.agt.sqr);
    join
    wait(env.scb.tran_index == seq_t.seq_count);
    //wait(env.con.num_processed + env.con.fifo_overflows == env.con.num_received);
    phase.drop_objection(this);
  endtask
endclass
