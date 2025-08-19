interface spi_slave_if (input logic clk_tb, input bit [7:0] SLAVE_RESET_RESPONSE);
  logic [7:0] slave_rx_data;
  logic [7:0] slave_tx_data;
  logic [3:0] idle_counter;
  bit [7:0] SLAVE_RESET_RESPONSE;

  modport slv_mon_mp (
    input slave_rx_data, clk_tb, idle_counter, slave_tx_data, SLAVE_RESET_RESPONSE
  );
endinterface