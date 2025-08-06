class bus_mon extends uvm_monitor;
  `uvm_component_utils(bus_mon)

  // Analysis port implementation to receive transactions
  uvm_analysis_imp #(bus_tran, bus_mon) mon_imp;
  uvm_analysis_port #(bus_tran) mon_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mon_imp = new("mon_imp", this);
    mon_ap = new("mon_ap", this);
  endfunction

  function void write(bus_tran tr);
    `uvm_info("MONITOR", $sformatf("Observed %0d/%0d %s transaction from DUT: addr=0x%2h, data=0x%8h, write=%0b",
                                   tr.seq_index, tr.seq_count, tr.seq_type, tr.addr, tr.data, tr.write),
                                   UVM_MEDIUM)

    mon_ap.write(tr);
  endfunction
endclass
