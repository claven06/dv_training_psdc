class spi_env extends uvm_env;
  `uvm_component_utils(spi_env)

  spi_agt agt;
  spi_scb scb;
  //bus_cov cov;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Set agent as active
    uvm_config_db#(uvm_active_passive_enum)::set(this, "agt", "is_active", UVM_ACTIVE);
    
    agt = spi_agt::type_id::create("agt", this);
    scb = spi_scb::type_id::create("scb", this);

    uvm_config_db#(virtual spi_if)::set(this, "scb", "vif", null);

  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    agt.agt_ap.connect(scb.scb_imp);
    //agt.agt_ap.connect(cov.cov_imp);
  endfunction
endclass
