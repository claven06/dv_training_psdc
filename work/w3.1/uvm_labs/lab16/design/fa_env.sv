class fa_env extends uvm_env;
  `uvm_component_utils(fa_env)

  fa_agt agt;
  fa_scb scb;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agt = fa_agt::type_id::create("agt", this);
    scb = fa_scb::type_id::create("scb", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    agt.agt_ap.connect(scb.scb_imp);
  endfunction
endclass
