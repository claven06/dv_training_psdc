class bus_drv extends uvm_driver #(bus_tran);
  `uvm_component_utils(bus_drv)

  uvm_analysis_port #(bus_tran) drv_ap;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    drv_ap = new("drv_ap", this);
  endfunction

  task run_phase(uvm_phase phase);
    bus_tran tr;
    forever begin
      seq_item_port.get_next_item(tr);

      drv_ap.write(tr);
      `uvm_info("DRIVER", $sformatf("Drive %0d/%0d %s transaction to DUT: addr=0x%2h, data=0x%8h, write=%0b",
                                    tr.seq_index, tr.seq_count, tr.seq_type, tr.addr, tr.data, tr.write),
                                    UVM_MEDIUM)

      seq_item_port.item_done();
    end
  endtask
endclass
