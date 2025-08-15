interface spi_if;

  // DUT inputs (driven by driver)
  logic        start;    
  logic [7:0]  tx_data;  
  logic		   clk;
  logic		   rst_n;
  // DUT outputs (sampled by monitor)
  logic [7:0]  rx_data;  
  logic        busy;     
  logic        done;     

  // SPI interface signals
  logic        sclk;     
  logic        mosi;     
  logic        miso;     
  logic        cs_n;     

  // === Clocking block for driver ===
  clocking drv_cb @(posedge clk);
    default input #1step output #1step;
    output start, tx_data, miso;  
    input  rx_data, busy, done;
    input  sclk, mosi, cs_n;
  endclocking

  // === Clocking block for monitor ===
  clocking mon_cb @(posedge clk);
    default input #1step output #1step;
    input start, tx_data, rx_data, busy, done;
    input sclk, mosi, miso, cs_n;
  endclocking


endinterface
