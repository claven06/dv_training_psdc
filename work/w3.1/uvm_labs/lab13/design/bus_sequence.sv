class bus_sequence extends uvm_sequence #(bus_transaction);
   `uvm_object_utils(bus_sequence)
   int seq_count;
   int min_delay;
   int max_delay;
   int delay;
   int sent_count;

   function new(string name = "bus_sequence");
      super.new(name);
      sent_count = 0;
   endfunction

   function int get_random_delay();
      return $urandom_range(min_delay, max_delay);
   endfunction

   task body();
      bus_transaction tr;
      `uvm_info(get_type_name(), "Normal Priority Sequence", UVM_MEDIUM)
      repeat (seq_count) begin
         tr = bus_transaction::type_id::create("tr");
         start_item(tr);
         assert(tr.randomize() with { addr[7:4] == 4'hA; write == 1; }); // Limit to write transactions only
         tr.seq_type = "normal";  // Lab 11
         delay = get_random_delay();  // Lab 11
         sent_count++;  // Lab 11
         `uvm_info(get_type_name(), $sformatf("Sent %0d/%0d %s sequences, next sequence after %0d", sent_count, seq_count, tr.seq_type, delay), UVM_MEDIUM)  // Lab 11
         #delay;  // Lab 11
         finish_item(tr);
      end
   endtask
endclass
