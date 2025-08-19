class spi_seq extends uvm_sequence #(spi_tran);
  `uvm_object_utils(spi_seq)

  function new(string name = "spi_seq");
    super.new(name);
  endfunction

  task body();
    spi_tran tr;
    repeat (4) begin
        tr = spi_tran::type_id::create("tr");
        start_item(tr);
        assert(tr.randomize());
        finish_item(tr);

        `uvm_info(get_type_name(), $sformatf("Sent rst_n=%0b, start=%0b, tx_data=%0b, miso=%0b", tr.rst_n, tr.start, tr.tx_data, tr.miso),UVM_MEDIUM)

    end
  endtask
endclass