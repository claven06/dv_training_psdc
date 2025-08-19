interface spi_if #(
     parameter CLK_DIV = 4
) (input logic clk_tb);
    logic          rst_n_tb;
    logic          start_tb;
    logic [7:0]    tx_data_tb;
    logic [7:0]    rx_data_tb;
    logic          busy_tb;
    logic          done_tb;
    logic          sclk_tb;
    logic          mosi_tb;
    logic          miso_tb;
    logic          cs_n_tb;

  // Modport for driver
    modport drv_mp (
        output start_tb, tx_data_tb, miso_tb, rst_n_tb,
        input rx_data_tb, busy_tb, done_tb, sclk_tb, mosi_tb, cs_n_tb,
        input clk_tb
    );

    // Modport for monitor
    modport mon_mp (
      input start_tb, tx_data_tb, miso_tb, rx_data_tb, busy_tb, done_tb, sclk_tb, mosi_tb, cs_n_tb, clk_tb, rst_n_tb // Monitor only reads
    );

endinterface

interface clk_if();
  logic clk_tb;

  initial clk_tb <= 0;

  always #10 clk_tb = ~clk_tb;
endinterface
