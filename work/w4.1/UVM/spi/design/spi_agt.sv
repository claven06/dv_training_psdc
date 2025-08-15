class spi_agt extends uvm_agent;

  // UVM automation macro
  `uvm_component_utils(spi_agt)

  uvm_analysis_port #(spi_tran) agt_ap;

  spi_drv  drv;
  spi_mon  mon;
  spi_sqr sqr;

  // Constructor
  function new(string name, uvm_component parent);
    super.new(name, parent);
	agt_ap = new("agt_ap", this);    
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    mon = spi_mon::type_id::create("mon", this);

    // Create driver & sequencer if agent is active
    if (get_is_active() == UVM_ACTIVE) begin
      drv  = spi_drv::type_id::create("drv", this);
      sqr = spi_sqr::type_id::create("seqr", this);
    end
  endfunction

  // Connect phase
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    mon.mon_ap.connect(agt_ap);
    if (get_is_active() == UVM_ACTIVE) begin
      drv.seq_item_port.connect(sqr.seq_item_export);
    end

  endfunction
endclass

