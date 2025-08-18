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


  // Done pulse must be 1 cycle
  property done_one_cycle_pulse;
    @(posedge clk) disable iff (!rst_n)
      done |-> ##1 !done;
  endproperty
  assert property (done_one_cycle_pulse)
    else $error("SPI protocol: 'done' not one cycle long");

  // SCLK must idle low when CS_n is high
  property sclk_idle_low;
    @(posedge clk) disable iff (!rst_n)
      (cs_n == 1) |-> (sclk == 0);
  endproperty
  assert property (sclk_idle_low)
    else $error("SPI protocol: SCLK not low when CS_n=1");


endinterface
