class fa_agt extends uvm_agent;
  `uvm_component_utils(fa_agt)

  uvm_analysis_port #(fa_tran) agt_ap;

  fa_drv drv;
  fa_mon mon;
  fa_sqr sqr;

  virtual fadder_if vif;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    agt_ap = new("agt_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Get interface from config DB
    if (!uvm_config_db#(virtual fadder_if)::get(this, "", "vif", vif)) begin
      `uvm_fatal("NO_VIF", "Failed to get vif from config DB")
    end

    mon = fa_mon::type_id::create("mon", this);
    mon.vif = vif;

    // Only create driver and sequencer if agent is active
    if (get_is_active() == UVM_ACTIVE) begin
      drv = fa_drv::type_id::create("drv", this);
      drv.vif = vif;
      sqr = fa_sqr::type_id::create("sqr", this);
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
  endfunction
endclass
