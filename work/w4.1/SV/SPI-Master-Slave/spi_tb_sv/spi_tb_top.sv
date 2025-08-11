module spi_tb_top;

localparam MASTER_FREQ = 100_000_000;
localparam SLAVE_FREQ = 1_800_000;
localparam SPI_MODE = 1;
localparam SPI_TRF_BIT = 8;

// Clock & reset signals
logic clk;
logic rst;

// Inputs
logic [1:0]                 req;
logic [7:0]                 wait_duration;
logic [SPI_TRF_BIT-1:0]     din_master;
logic [SPI_TRF_BIT-1:0]     din_slave;

// Outputs
logic [SPI_TRF_BIT-1:0]     dout_master;
logic [SPI_TRF_BIT-1:0]     dout_slave;
logic                       done_tx;
logic                       done_rx;

// Clock generation
initial begin
    clk = 0;
    forever #5 clk= ~clk;
end

// DUT instantiation
spi_top #(
    .MASTER_FREQ(MASTER_FREQ),
    .SLAVE_FREQ(SLAVE_FREQ),
    .SPI_MODE(SPI_MODE),
    .SPI_TRF_BIT(SPI_TRF_BIT)
) dut ( .* );





// Main
initial begin
    wait_duration = '0;
    din_master = '0;
    din_slave = '0;
    rst = 0;

    `ifdef TEST_1
    `endif
end


endmodule

