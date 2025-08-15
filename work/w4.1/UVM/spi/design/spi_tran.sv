class spi_tran extends uvm_sequence_item;
 
  rand bit [7:0] tx_data;     
       bit [7:0] rx_data;     
  rand bit       start;      
       bit       done;        
	   bit 		 busy;
	   bit		 mosi;
       bit		 miso;
	   bit 		 sclk;
	   bit		 cs_n;
	  int seq_count;
	  int seq_index;


  `uvm_object_utils(spi_tran)

  function new(string name = "spi_tran");
    super.new(name);
  endfunction

endclass
