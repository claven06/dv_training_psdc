class bus_test extends uvm_test;
   `uvm_component_utils(bus_test)

   bus_sequencer sqr;
   bus_driver drv;
   bus_sequence seq;
   high_prio_seq hseq;
   low_prio_seq lseq;

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      sqr = bus_sequencer::type_id::create("sqr", this);
      drv = bus_driver::type_id::create("drv", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      drv.seq_item_port.connect(sqr.seq_item_export);
   endfunction

   virtual task run_phase(uvm_phase phase);
      seq = bus_sequence::type_id::create("seq");
      hseq = high_prio_seq::type_id::create("hseq");
      lseq = low_prio_seq::type_id::create("lseq");
      `uvm_info("BTOP/TEST", "Launching the sequence", UVM_MEDIUM);
      phase.raise_objection(this);
      fork
        seq.start(sqr); // Launch the sequence
        hseq.start(sqr);
        lseq.start(sqr);
      join
      phase.drop_objection(this);
   endtask
endclass

