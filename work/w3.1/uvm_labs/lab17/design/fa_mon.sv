class bus_mon extends uvm_monitor;
  `uvm_component_utils(bus_mon)

  int tran_count;
  int tran_index;
  string tran_type;
  string tran_dir;

  virtual bus_ctrl_if.mon_mp vif;  // Use mon_mp
  //virtual bus_ctrl_if vif;

  uvm_analysis_port #(bus_tran) mon_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mon_ap = new("mon_ap", this);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    //if(!uvm_config_db#(virtual bus_ctrl_if)::get(this, "", "vif", vif)) begin
    //  `uvm_error("MONITOR", "Virtual interface (mon_cb) not found in config db")
    //end
    if(!uvm_config_db#(virtual bus_ctrl_if.mon_mp)::get(this, "", "vif", vif)) begin
      `uvm_error("MONITOR", "Virtual interface (mon_mp) not found in config db")
    end
  endfunction

  task run_phase(uvm_phase phase);
    bus_tran tr_dut;
    forever begin
      // The property will be evaluated at every positive edge of the clock signal
      // But only if the condition is true at that clock edge
      @(vif.mon_cb iff (vif.mon_cb.ready));

      // Create and populate transaction
      tr_dut = bus_tran::type_id::create("tr_dut");
      tr_dut.addr = vif.mon_cb.addr_tb;
      tr_dut.data = vif.mon_cb.write_tb ? vif.mon_cb.wdata_tb : vif.mon_cb.rdata;
      tr_dut.write = vif.mon_cb.write_tb;

      if(!uvm_config_db#(int)::get(null, "", "tran_count", tran_count)) begin
        `uvm_warning("MONITOR", "Unable to retrieve tran_count from bus_drv")
      end
      if(!uvm_config_db#(int)::get(null, "", "tran_index", tran_index)) begin
        `uvm_warning("MONITOR", "Unable to retrieve tran_count from bus_drv")
      end
      if(!uvm_config_db#(string)::get(null, "", "tran_type", tran_type)) begin
        `uvm_warning("MONITOR", "Unable to retrieve tran_type from bus_drv")
      end
      if(!uvm_config_db#(string)::get(null, "", "tran_dir", tran_dir)) begin
        `uvm_warning("MONITOR", "Unable to retrieve tran_type from bus_drv")
      end

      `uvm_info("MONITOR", $sformatf("Observe %s %0d/%0d %s tran from DUT: addr=0x%2h, data=0x%8h, write=%0b",
                                     tran_dir, tran_index, tran_count,
                                     tran_type, tr_dut.addr, tr_dut.data, tr_dut.write), UVM_MEDIUM)

      tr_dut.tran_count = this.tran_count;
      tr_dut.tran_index = this.tran_index;
      tr_dut.tran_type = this.tran_type;
      tr_dut.tran_dir = this.tran_dir;
      tr_dut.tran_ready = vif.ready;
      mon_ap.write(tr_dut);
    end
  endtask
endclass

