class bus_agent extends uvm_agent;
   `uvm_component_utils(bus_agent)

   uvm_analysis_port #(bus_transaction) ap_port;

   bus_driver    drv;
   bus_monitor   mon;
   bus_sequencer sqr;

   function new(string name, uvm_component parent);
      super.new(name, parent);
      ap_port = new("ap_port", this);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      mon = bus_monitor::type_id::create("mon", this);

      // Only create driver and sequencer if agent is active
      if (get_is_active() == UVM_ACTIVE) begin
         drv = bus_driver::type_id::create("drv", this);
         sqr = bus_sequencer::type_id::create("sqr", this);
      end
   endfunction

   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);

      // Connect driver's analysis port to monitor's implementation
      if (get_is_active() == UVM_ACTIVE) begin
         drv.ap.connect(mon.ap_implementation);
      end

      // Connect driver to sequencer if active
      if (get_is_active() == UVM_ACTIVE) begin
         drv.seq_item_port.connect(sqr.seq_item_export);
      end

      // Connect monitor's analysis port to agent's analysis port
      mon.ap_port.connect(ap_port);
   endfunction
endclass

