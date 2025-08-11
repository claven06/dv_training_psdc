class fa_cov extends uvm_component;
  `uvm_component_utils(fa_cov)

  // Use implementation port to receive transactions
  uvm_analysis_imp #(fa_tran, fa_cov) cov_imp;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    cov_imp = new("cov_imp", this);
    fa_cg = new();
    fa_cg.set_inst_name($sformatf("%s\ (fa_cg\)", get_full_name()));
  endfunction

  // This will be called when transactions arrive
  function void write(fa_tran tr);
    fa_cg.sample(tr);
  endfunction

  covergroup fa_cg with function sample(fa_tran tr);
    option.per_instance = 1;
    option.comment = "THIS IS MY FA_CG COVERAGE";

    a_cp: coverpoint tr.a;
    b_cp: coverpoint tr.b;
    cin_cp: coverpoint tr.cin;
    sum_cp: coverpoint tr.sum;
    cout_cp: coverpoint tr.cout;
    abcin_cp: cross a_cp, b_cp, cin_cp;

  endgroup

  function void report_phase(uvm_phase phase);
    `uvm_info("COVERAGE", $sformatf("Coverage fa_cg      : %.2f%%", fa_cg.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage a_cp      : %.2f%%", fa_cg.a_cp.get_inst_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage b_cp      : %.2f%%", fa_cg.b_cp.get_inst_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage cin_cp      : %.2f%%", fa_cg.cin_cp.get_inst_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage sum_cp      : %.2f%%", fa_cg.sum_cp.get_inst_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage cout_cp      : %.2f%%", fa_cg.cout_cp.get_inst_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage abcin_cp      : %.2f%%", fa_cg.abcin_cp.get_inst_coverage()), UVM_NONE)
  endfunction
endclass
