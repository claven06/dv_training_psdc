class bus_monitor extends uvm_component;
   `uvm_component_utils(bus_monitor)

   // Analysis port implementation to receive transactions
   uvm_analysis_imp #(bus_transaction, bus_monitor) ap_implementation;

   function new(string name, uvm_component parent);
      super.new(name, parent);
      ap_implementation = new("ap_implementation", this);
   endfunction

   function void write(bus_transaction tr);
      `uvm_info("MONITOR",
                $sformatf("Observed transaction: addr=0x%2h, data=0x%8h, write=%0b",
                          tr.addr, tr.data, tr.write),
                UVM_LOW)
   endfunction
endclass
