class bus_driver extends uvm_driver #(bus_transaction);
   `uvm_component_utils(bus_driver)

   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

   virtual task run_phase(uvm_phase phase);
      bus_transaction tr;

      forever begin
         seq_item_port.get_next_item(tr);

         `uvm_info("DRIVER",
                   $sformatf("Driving transaction: addr = 0x%0h, data = 0x%0h, write = %0b",
                             tr.addr, tr.data, tr.write),
                   UVM_MEDIUM)

         // Simulate DUT interaction here

         #10 seq_item_port.item_done();
      end
   endtask
endclass
