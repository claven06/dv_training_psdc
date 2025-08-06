`include "uvm_macros.svh"

package ptop_child_pkg;

    import uvm_pkg::*;

    class ptop_child extends uvm_component;
        `uvm_component_utils(ptop_child)

        function new (string name, uvm_component parent);
            super.new(name, parent);
            `uvm_info("PTOP/CHILD/NEW", $sformatf("Creating %s", name), UVM_LOW)
        endfunction

    	function void build_phase(uvm_phase phase);
      	    super.build_phase(phase);
            `uvm_info("PTOP/CHILD/BUILD", "Executing build_phase", UVM_MEDIUM)
    	endfunction

    	function void connect_phase(uvm_phase phase);
            super.connect_phase(phase);
            `uvm_info("PTOP/CHILD/CONNECT", "Executing connect_phase", UVM_MEDIUM)
    	endfunction

        // Objection
        task run_phase(uvm_phase phase);
          phase.raise_objection(this);
          super.run_phase(phase);
          `uvm_info("PTOP/CHILD/RUN", "Child run phase started", UVM_MEDIUM)

          #50ns; // Simulate some child activity

          `uvm_info("PTOP/CHILD/RUN", "Child run phase completed", UVM_MEDIUM)
          phase.drop_objection(this);
        endtask
    endclass
endpackage
