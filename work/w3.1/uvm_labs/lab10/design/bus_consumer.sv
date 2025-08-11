class bus_consumer extends uvm_component;
   `uvm_component_utils(bus_consumer)

   uvm_put_imp #(bus_transaction, bus_consumer) put_imp;

   // Counter and error flag
   int num_received;
   int num_errors;

   function new(string name, uvm_component parent);
      super.new(name, parent);
      put_imp = new("put_imp", this);
      num_received = 0;
      num_errors = 0;
   endfunction

   // Required by uvm_put_imp to have put(), can_put() and try_out()
   function bit can_put();
      return 1; // Always ready to receive
   endfunction

   function bit try_put(bus_transaction tr);
      put(tr);
      return 1;
   endfunction

   // Receive transactions here
   virtual function void put(bus_transaction tr);
      num_received++;

      `uvm_info("CONSUMER",
                $sformatf("Received transaction: addr=0x%2h, data=0x%8h, write=%0b",
                          tr.addr, tr.data, tr.write),
                UVM_LOW)

      // Example check: write should be 1
      if (tr.write == 0) begin
         num_errors++;
         `uvm_error("CONSUMER_CHECK",
                    $sformatf("Invalid transaction! addr=0x%2h, data=0x%8h, write=%0b <<<<<<<<<<<<<<<<",
                              tr.addr, tr.data, tr.write))
      end
   endfunction

   // Print summary at end of simulation
   function void report_phase(uvm_phase phase);
      `uvm_info("CONSUMER_REPORT",
                $sformatf("Total received transactions: %0d", num_received),
                UVM_NONE)
      `uvm_info("CONSUMER_REPORT",
                $sformatf("Total errors detected: %0d", num_errors),
                UVM_NONE)
   endfunction
endclass


