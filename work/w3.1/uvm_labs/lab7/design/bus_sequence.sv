class bus_sequence extends uvm_sequence #(bus_transaction);
   `uvm_object_utils(bus_sequence)

   function new(string name = "bus_sequence");
      super.new(name);
   endfunction

   task body();
      bus_transaction tr;
      `uvm_info(get_type_name(), "Normal Priority Sequence", UVM_MEDIUM)
      repeat (7) begin
         tr = bus_transaction::type_id::create("tr");
         start_item(tr);
         assert(tr.randomize() with { addr[7:4] == 4'hA; write == 1; }); // Limit to write transactions only
         finish_item(tr);
      end
   endtask
endclass
