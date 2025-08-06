`include "uvm_macros.svh"

package ptop_parent_pkg;

  import uvm_pkg::*;
  import ptop_child_pkg::*;  // Parent depends on child

  class ptop_parent extends uvm_component;
    `uvm_component_utils(ptop_parent)
    
    ptop_child child;

    function new(string name, uvm_component parent);
      super.new(name, parent);
      `uvm_info("PTOP/PARENT/NEW", $sformatf("Creating %s", name), UVM_LOW)
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info("PTOP/PARENT/BUILD", "Start of build_phase", UVM_MEDIUM)
      child = ptop_child::type_id::create("child", this);
      parent_done = 0;    // Hierachical objection
      `uvm_info("PTOP/PARENT/BUILD", "End of build_phase", UVM_MEDIUM)
    endfunction

    function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      `uvm_info("PTOP/PARENT/CONNECT", "Start of connect_phase", UVM_MEDIUM)
      `uvm_info("PTOP/PARENT/CONNECT", "End of connect_phase", UVM_MEDIUM)
    endfunction

    // Objection with timeout
    bit parent_done;
    task run_phase(uvm_phase phase);
      phase.raise_objection(this, "Parent starting");

      fork
        begin
          `uvm_info("PTOP/PARENT/RUN", "Parent activity started", UVM_MEDIUM)
          #150ns;
          parent_done = 1;
          `uvm_info("PTOP/PARENT/RUN", "Parent activity completed", UVM_MEDIUM)
          phase.drop_objection(this, "Parent completed");
        end

        begin
          #100ns;
          if (!parent_done) begin
            `uvm_warning("PTOP/PARENT/TIMEOUT", "Parent activity taking too long")
          end
        end
      join
    endtask
  endclass

endpackage
