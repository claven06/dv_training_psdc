package top_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  // Build class
  class base_build extends uvm_component;
    `uvm_component_utils(base_build)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info("BUILD", "Build phase executed", UVM_LOW)
    endfunction

  endclass

  // Test class
  class top_first_test extends uvm_test;
    `uvm_component_utils(top_first_test)

    function new(string name, uvm_component parent);
      super.new(name, parent);
    endfunction

    base_build bb;

    virtual function void build_phase(uvm_phase phase);
      super.build_phase(phase);

      // Create the base_build instance here
      bb = base_build::type_id::create("bb", this);
    endfunction

    virtual task run_phase(uvm_phase phase);
      super.run_phase(phase);

      `uvm_info("TEST", "Hello UVM World!", UVM_LOW)
      `uvm_warning("TEST", "Hello UVM World!")
      `uvm_error("TEST", "Hello UVM World!")
      //`uvm_fatal("TEST", "Hello UVM World!")
      `uvm_info("TEST", $sformatf("Factory returned test of type=%s, path=%s", bb.get_type_name(), bb.get_full_name()), UVM_LOW)
    endtask
  endclass

endpackage
