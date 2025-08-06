`include "uvm_macros.svh"

package ptop_test_pkg;

    import uvm_pkg::*;
    import ptop_parent_pkg::*;

    class ptop_test extends uvm_test;
        `uvm_component_utils(ptop_test)

        ptop_parent parent;

        function new (string name, uvm_component parent);
            super.new (name, parent);
            `uvm_info("PTOP/TEST/NEW", $sformatf("Creating %s", name), UVM_LOW)
        endfunction

        function void build_phase(uvm_phase phase);
          super.build_phase(phase);
          `uvm_info("PTOP/TEST/BUILD", "Start of build_phase", UVM_MEDIUM)
          parent = ptop_parent::type_id::create("parent", this);
          `uvm_info("PTOP/TEST/BUILD", "End of build_phase", UVM_MEDIUM)
        endfunction

        function void end_of_elaboration_phase(uvm_phase phase);
          super.end_of_elaboration_phase(phase);
          `uvm_info("PTOP/TEST/ENDOFELAB", "Printing test topology", UVM_MEDIUM)
          print();
        endfunction

        function void extract_phase(uvm_phase phase);
          super.extract_phase(phase);
          `uvm_info("PTOP/TEST/EXTRACT", "In the extract phase", UVM_MEDIUM)
        endfunction

        // Objection
        task run_phase(uvm_phase phase);
          phase.raise_objection(this);
          super.run_phase(phase);
          `uvm_info("PTOP/TEST/RUN", "Test run phase started", UVM_MEDIUM)

          #15ns; // Simulate some test activity

          `uvm_info("PTOP/TEST/RUN", "Test run phase completed", UVM_MEDIUM)
          phase.drop_objection(this);
        endtask
    endclass
endpackage
