class spi_tran extends uvm_sequence_item;
  //inputs
  rand logic rst_n;
  rand logic start;
  rand logic [7:0] tx_data;
  //rand logic miso;
  logic miso;

  //outputs
  logic clk;
  logic [7:0] rx_data;
  logic busy;
  logic done;
  logic sclk;
  logic mosi;
  logic cs_n;

  logic [7:0] slave_rx_data;
  logic [7:0] slave_tx_data;
  
  constraint c_rst_n   { rst_n == 1; }
  //constraint c_start   { start == 1; } //start=0, test hang due to state always in IDLE and done will nvr go high

  //constraint c_miso   { miso == 1; } 
  //constraint c_tx_data { tx_data inside {[8'h00:8'hFF]}; }
  

  `uvm_object_utils(spi_tran)

  function new(string name = "spi_tran");
    super.new(name);
  endfunction
endclass
