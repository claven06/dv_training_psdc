class spi_seq extends uvm_sequence #(spi_tran);
  `uvm_object_utils(spi_seq)
  int seq_count;
  int seq_index;


  function new(string name = "spi_seq");
    super.new(name);
  endfunction

  task body();
    spi_tran tr;

    repeat (20) begin
      tr = spi_tran::type_id::create("tr");
 
      start_item(tr);

	  tr.randomize();
	  //tr.start = 1;
	  tr.seq_count = this.seq_count;
      tr.seq_index = this.seq_index;

      finish_item(tr);


	  `uvm_info(get_type_name(), $sformatf("Sent %0d/%0d tx_data=%0h, start=%0d, miso=%0b",seq_index, seq_count, tr.tx_data, tr.start, tr.miso),
                                           UVM_MEDIUM)

	seq_index++;
    end
  endtask
endclass
