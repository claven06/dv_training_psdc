`include "uvm_macros.svh"

package ptop_test_pkg;

  import uvm_pkg::*;
  import ptop_parent_pkg::*;  // Test depends on parent

  class ptop_test extends uvm_test;
    `uvm_component_utils(ptop_test)

    ptop_parent parent;
    uvm_phase run_ph, extract_ph, check_ph, report_ph, final_ph;    // Phase jump

    function new(string name, uvm_component parent);
      super.new(name, parent);
      `uvm_info("PTOP/TEST/NEW", $sformatf("Creating %s", name), UVM_LOW)
    endfunction

    function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      `uvm_info("PTOP/TEST/BUILD", "Start of build_phase", UVM_MEDIUM)
      parent = ptop_parent::type_id::create("parent", this);
      // Phase jump: get phase handles
      run_ph = uvm_run_phase::get();
      extract_ph = uvm_extract_phase::get();
      check_ph = uvm_check_phase::get();
      report_ph = uvm_report_phase::get();
      final_ph = uvm_final_phase::get();
      `uvm_info("PTOP/TEST/BUILD", "End of build_phase", UVM_MEDIUM)
    endfunction

    function void end_of_elaboration_phase(uvm_phase phase);
      super.end_of_elaboration_phase(phase);
      `uvm_info("PTOP/TEST/ENDOFELAB", "Printing test topology", UVM_MEDIUM)
      print();
    endfunction

        // Phase jump
    task run_phase(uvm_phase phase);
      phase.raise_objection(this);
      `uvm_info("PTOP/TEST/RUN", "Start of run_phase", UVM_MEDIUM)

      #50ns; // Simulate some test activity

      // Proper phase jump through the correct sequence
      `uvm_info("PTOP/TEST/PHASE", "Initiating controlled phase jump", UVM_HIGH)
      phase.jump(report_ph); // Must go through extract->check->report->final

      `uvm_info("PTOP/TEST/RUN", "End of run_phase", UVM_MEDIUM)
      phase.drop_objection(this);
    endtask

    virtual function void extract_phase(uvm_phase phase);
      `uvm_info("PTOP/TEST/EXTRACT", "In extract phase", UVM_MEDIUM)
    endfunction

    virtual function void check_phase(uvm_phase phase);
      `uvm_info("PTOP/TEST/CHECK", "In check phase", UVM_MEDIUM)
    endfunction

    virtual function void report_phase(uvm_phase phase);
      `uvm_info("PTOP/TEST/REPORT", "In report phase", UVM_MEDIUM)
    endfunction

    virtual function void final_phase(uvm_phase phase);
      `uvm_info("PTOP/TEST/FINAL", "In final phase", UVM_MEDIUM)
      `uvm_info("PTOP/TEST/FINAL", "End of final phase", UVM_MEDIUM)
    endfunction
  endclass

endpackage

