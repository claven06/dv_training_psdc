class bus_tran extends uvm_sequence_item;
  rand bit [7:0] addr;
  rand bit [31:0] data;
  rand bit write;
  int seq_count;
  int seq_index;
  string seq_type;

  `uvm_object_utils(bus_tran)

  function new(string name = "bus_tran");
    super.new(name);
  endfunction
endclass
