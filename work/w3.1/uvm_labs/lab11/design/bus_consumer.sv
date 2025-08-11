class bus_consumer extends uvm_component;
   `uvm_component_utils(bus_consumer)

   uvm_put_imp #(bus_transaction, bus_consumer) put_imp;

   // FIFO related settings
   local bus_transaction fifo[$];
   local int fifo_size = 2;  // Set your desired FIFO size
   local int fifo_process_time = 10;  // Set your desired FIFO process time
   int fifo_overflows = 0;
   int fifo_max_consumed = 0;

   // Counters
   int num_received;
   int num_processed;
   int num_errors;

   // Contructors
   function new(string name, uvm_component parent);
      super.new(name, parent);
      put_imp = new("put_imp", this);
      num_received = 0;
      num_processed = 0;
      num_errors = 0;
      fifo_overflows = 0;
      fifo_max_consumed = 0;
      `uvm_info("FIFO_INFO", $sformatf("FIFO Size: %0d", fifo_size), UVM_MEDIUM)
      `uvm_info("FIFO_INFO", $sformatf("FIFO Process Time: %0d", fifo_process_time), UVM_MEDIUM)
   endfunction

   // Required by uvm_put_imp to have put(), can_put() and try_out()
   function bit can_put();
      return (fifo.size() < fifo_size);
   endfunction
   function bit try_put(bus_transaction tr);
      if (can_put()) begin
         put(tr);
         return 1;
      end
      return 0;
   endfunction
   // Receive transactions here and store in FIFO
   virtual function void put(bus_transaction tr);
      num_received++;

      // Maximum FIFO utilization
      if (fifo.size() + 1 >= fifo_max_consumed) begin
         fifo_max_consumed = fifo.size() + 1;
      end

      // FIFO overflow
      if (fifo.size() >= fifo_size) begin
         fifo_overflows++;
         `uvm_error("FIFO_OVERFLOW", $sformatf("FIFO overflow! Discarding transaction: addr=0x%2h, data=0x%8h, write=%0b >>>>>>>>>>>>>>>>",
		    tr.addr, tr.data, tr.write))
         return;
      end

      fifo.push_back(tr);  // Push the transaction into the back of FIFO
      `uvm_info("FIFO_ADD",
                $sformatf("Added to FIFO (size=%0d): addr=0x%2h, data=0x%8h, write=%0b",
                          fifo.size(), tr.addr, tr.data, tr.write),
                UVM_MEDIUM)

      // Start processing if this is the first item
      if (fifo.size() == 1) begin
         fork
            process_fifo();
         join_none
      end
   endfunction

   // Process transactions from FIFO
   local task process_fifo();
      bus_transaction tr;
      while (fifo.size() > 0) begin
         #fifo_process_time;  // Simulate processing delay
	 num_processed++;

         tr = fifo.pop_front();  // Retrieve the transaction from the front of FIFO
         `uvm_info("FIFO_PROCESS",
                   $sformatf("Processing from FIFO (remaining=%0d): addr=0x%2h, data=0x%8h, write=%0b",
                             fifo.size(), tr.addr, tr.data, tr.write),
                   UVM_MEDIUM)

         // Example check: write should be 1
         if (tr.write == 0) begin
            num_errors++;
            `uvm_error("CONSUMER_CHECK",
                       $sformatf("Invalid transaction! addr=0x%2h, data=0x%8h, write=%0b <<<<<<<<<<<<<<<<",
		       tr.addr, tr.data, tr.write))
         end
      end
   endtask

   // Print summary at end of simulation
   function void report_phase(uvm_phase phase);
      `uvm_info("CONSUMER_REPORT",
                $sformatf("Total received transactions: %0d", num_received),
                UVM_NONE)
      `uvm_info("CONSUMER_REPORT",
                $sformatf("Total processed transactions: %0d", num_processed),
                UVM_NONE)
      `uvm_info("CONSUMER_REPORT",
                $sformatf("Total errors detected: %0d", num_errors),
                UVM_NONE)
      `uvm_info("CONSUMER_REPORT",
                $sformatf("FIFO overflows: %0d", fifo_overflows),
                UVM_NONE)
      `uvm_info("CONSUMER_REPORT",
                $sformatf("Maximum FIFO utilization: %0d/%0d", fifo_max_consumed, fifo_size),
                UVM_NONE)
   endfunction
endclass

