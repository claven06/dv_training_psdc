class bus_agt extends uvm_agent;
  `uvm_component_utils(bus_agt)

  uvm_analysis_port #(bus_tran) agt_ap;

  bus_drv drv;
  bus_mon mon;
  bus_sqr sqr;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    agt_ap = new("agt_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon = bus_mon::type_id::create("mon", this);
    // Only create driver and sequencer if agent is active
    if (get_is_active() == UVM_ACTIVE) begin
      drv = bus_drv::type_id::create("drv", this);
      sqr = bus_sqr::type_id::create("sqr", this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // Connect monitor's analysis port to agent's analysis port
    mon.mon_ap.connect(agt_ap);
    // Connect driver to sequencer if agent active
    if (get_is_active() == UVM_ACTIVE) begin
      drv.seq_item_port.connect(sqr.seq_item_export);
    end
    // Connect driver's analysis port to monitor's implementation if agent active
    // This is for demo purpose as there is no DUT. Monitor should connect to DUT
    if (get_is_active() == UVM_ACTIVE) begin
      drv.drv_ap.connect(mon.mon_imp);
    end
  endfunction
endclass
