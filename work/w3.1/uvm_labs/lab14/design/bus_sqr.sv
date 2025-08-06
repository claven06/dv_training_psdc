class bus_sqr extends uvm_sequencer #(bus_tran);
  `uvm_component_utils(bus_sqr)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
endclass
