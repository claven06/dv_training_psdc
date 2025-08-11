class bus_drv extends uvm_driver #(bus_tran);
  `uvm_component_utils(bus_drv)

  //virtual bus_ctrl_if vif;
  virtual bus_ctrl_if vif;

  uvm_analysis_port #(bus_tran) drv_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    drv_ap = new("drv_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    //if(!uvm_config_db#(virtual bus_ctrl_if)::get(this, "", "vif", vif)) begin
    //  `uvm_error("DRIVER", "Virtual interface (drv_cb) not found in config db")
    //end
    if(!uvm_config_db#(virtual bus_ctrl_if)::get(this, "", "vif", vif)) begin
      `uvm_error("DRIVER", "Virtual interface not found in config db")
    end
  endfunction

  task run_phase(uvm_phase phase);
    bus_tran tr;
    forever begin
      seq_item_port.get_next_item(tr);
      `uvm_info("DRIVER", $sformatf("Drive %s %0d/%0d %s tran to DUT: addr=0x%2h, wdata=0x%8h, write=%0b",
                                    tr.seq_dir, tr.seq_index, tr.seq_count,
                                    tr.seq_type, tr.addr, tr.data, tr.write), UVM_MEDIUM)
      @(vif.drv_cb);
      vif.drv_cb.reset_n_tb <= 1'b1;  // Ensure reset is inactive
      vif.drv_cb.valid_tb <= 1'b1;
      vif.drv_cb.addr_tb <= tr.addr;
      vif.drv_cb.wdata_tb <= tr.data;
      vif.drv_cb.write_tb <= tr.write;

      // Wait for DUT ready
      while (!vif.drv_cb.ready) @(vif.drv_cb);

      // Complete transaction
      @(vif.drv_cb);
      vif.drv_cb.valid_tb <= 1'b0;

      seq_item_port.item_done();
      uvm_config_db#(int)::set(null, "*", "tran_count", tr.seq_count);
      uvm_config_db#(int)::set(null, "*", "tran_index", tr.seq_index);
      uvm_config_db#(string)::set(null, "*", "tran_type", tr.seq_type);
      uvm_config_db#(string)::set(null, "*", "tran_dir", tr.seq_dir);
    end
  endtask
endclass
