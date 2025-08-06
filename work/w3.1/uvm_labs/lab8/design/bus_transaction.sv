`include "uvm_macros.svh"

import uvm_pkg::*;

class bus_transaction extends uvm_sequence_item;
   rand bit [7:0] addr;
   rand bit [31:0] data;
   rand bit write;

   `uvm_object_utils(bus_transaction)

   function new(string name = "bus_transaction");
      super.new(name);
   endfunction
endclass
