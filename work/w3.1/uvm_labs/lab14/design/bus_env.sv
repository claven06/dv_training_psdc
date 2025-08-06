class bus_env extends uvm_env;
  `uvm_component_utils(bus_env)

  bus_agt agt;
  bus_con con;
  bus_scb scb;
  bus_cov cov;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agt = bus_agt::type_id::create("agt", this);
    con = bus_con::type_id::create("con", this);
    scb = bus_scb::type_id::create("scb", this);
    cov = bus_cov::type_id::create("cov", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    agt.agt_ap.connect(con.con_imp);
    agt.agt_ap.connect(scb.mon_imp);
    agt.agt_ap.connect(cov.cov_imp);
  endfunction
endclass
