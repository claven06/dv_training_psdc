class bus_env extends uvm_env;
   `uvm_component_utils(bus_env)

   // Analysis port export to forward transactions
   uvm_analysis_export #(bus_transaction) ap_export;

   bus_driver drv;
   bus_monitor mon;
   bus_sequencer sqr;

   function new(string name, uvm_component parent);
      super.new(name, parent);
      ap_export = new("ap_export", this);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      drv = bus_driver::type_id::create("drv", this);
      mon = bus_monitor::type_id::create("mon", this);
      sqr = bus_sequencer::type_id::create("sqr", this);
   endfunction

   function void connect_phase(uvm_phase phase);
      // Connect driver sequencer
      drv.seq_item_port.connect(sqr.seq_item_export);

      // Connect driver analysis port to export
      drv.ap.connect(ap_export);

      // Connect analysis port export to monitor's implementation
      ap_export.connect(mon.ap_implementation);
   endfunction
endclass
