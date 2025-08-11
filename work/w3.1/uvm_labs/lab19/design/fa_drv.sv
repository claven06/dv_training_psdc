class fa_drv extends uvm_driver #(fa_tran);
  `uvm_component_utils(fa_drv)

  virtual fadder_if vif;
  //virtual fadder_if.drv_mp vif;

  uvm_analysis_port #(fa_tran) drv_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    drv_ap = new("drv_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if(!uvm_config_db#(virtual fadder_if)::get(this, "", "vif", vif)) begin
      `uvm_error("DRIVER", "Virtual interface (drv_cb) not found in config db")
    end
    //if(!uvm_config_db#(virtual fadder_if.drv_mp)::get(this, "", "vif", vif)) begin
    //  `uvm_error("DRIVER", "Virtual interface (drv_mp) not found in config db")
    //end
  endfunction

  task run_phase(uvm_phase phase);
    fa_tran tr;
    forever begin
      seq_item_port.get_next_item(tr);

      //@(vif.drv_cb);                // Wait for the posedge clock
      @(posedge vif.clk_tb);

      `uvm_info("DRIVER", $sformatf("Drive %0d/%0d %s tran to DUT: a=%0b, b=%0b, cin=%0b",
                                    tr.seq_index, tr.seq_count, tr.seq_type, tr.a, tr.b, tr.cin),
                                    UVM_MEDIUM)

      vif.drv_cb.a_tb <= tr.a;      // Drive 'a' from transaction (tr) to DUT
      vif.drv_cb.b_tb <= tr.b;      // Drive 'b' from transaction (tr) to DUT
      vif.drv_cb.cin_tb <= tr.cin;  // Drive 'cin' from transaction (tr) to DUT

      seq_item_port.item_done();
      uvm_config_db#(int)::set(null, "*", "tran_count", tr.seq_count);
      uvm_config_db#(int)::set(null, "*", "tran_index", tr.seq_index);
      uvm_config_db#(string)::set(null, "*", "tran_type", tr.seq_type);
    end
  endtask
endclass
