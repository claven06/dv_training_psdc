class bus_test extends uvm_test;
  `uvm_component_utils(bus_test)

  bus_env env;
  bus_seq seq;
  high_prio_seq hseq;
  low_prio_seq lseq;

  int seq_count = 8, hseq_count = 2, lseq_count = 5;
  int seq_min_delay = 10,  seq_max_delay = 15;
  int hseq_min_delay = 0, hseq_max_delay = 5;
  int lseq_min_delay = 5, lseq_max_delay = 10;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = bus_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    seq = bus_seq::type_id::create("seq");
    hseq = high_prio_seq::type_id::create("hseq");
    lseq = low_prio_seq::type_id::create("lseq");

    seq.seq_count = this.seq_count;
    seq.min_delay = this.seq_min_delay;
    seq.max_delay = this.seq_max_delay;
    hseq.seq_count = this.hseq_count;
    hseq.min_delay = this.hseq_min_delay;
    hseq.max_delay = this.hseq_max_delay;
    lseq.seq_count = this.lseq_count;
    lseq.min_delay = this.lseq_min_delay;
    lseq.max_delay = this.lseq_max_delay;

    `uvm_info("TEST", $sformatf("Starting sequences with config:\n\
                                Normal: count=%0d, delay=%0d-%0d\n\
                                High: count=%0d, delay=%0d-%0d\n\
                                Low: count=%0d, delay=%0d-%0d",
                                seq.seq_count, seq.min_delay, seq.max_delay,
                                hseq.seq_count, hseq.min_delay, hseq.max_delay,
                                lseq.seq_count, lseq.min_delay, lseq.max_delay),
                                UVM_MEDIUM)

    phase.raise_objection(this);
    fork
      seq.start(env.agt.sqr);
      hseq.start(env.agt.sqr);
      lseq.start(env.agt.sqr);
    join
    // Important to avoid simulation ended before processing all the FIFO contents
    wait(env.con.num_processed + env.con.fifo_overflows == env.con.num_received);
    phase.drop_objection(this);
  endtask
endclass
