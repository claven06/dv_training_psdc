module spi_tb_top;

localparam MASTER_FREQ = 100_000_000;
localparam SLAVE_FREQ = 3_700_000; // Modified from 1,800,000 to achieve spec
localparam SPI_MODE = 1;
localparam SPI_TRF_BIT = 8;

localparam TEST_ITERATION = 5;

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

// Testbench signals
logic ref_sclk;

// Clock generation
initial begin
    clk = 0;
    forever #5 clk= ~clk; // 100MHz clock
end

initial begin
    ref_sclk = 0;
    forever #135.135 ref_sclk = ~ref_sclk; // 3.7MHz clock
end

// DUT instantiation
spi_top #(
    .MASTER_FREQ(MASTER_FREQ),
    .SLAVE_FREQ(SLAVE_FREQ),
    .SPI_MODE(SPI_MODE),
    .SPI_TRF_BIT(SPI_TRF_BIT)
) dut ( .* );

// FSDB generation
initial begin
    $fsdbDumpfile("dump.fsdb");
    $fsdbDumpvars(0, spi_tb_top);
    $fsdbDumpMDA();
    $fsdbDumpSVA();
end

// Assertions
AST_RST_ALL_OUTPUT_ZERO : assert property (@(posedge clk) (
                            (rst) |-> ((dout_master == '0) && (dout_slave == '0) && (done_tx == '0) && (done_rx == '0))));

// Main
initial begin
    wait_duration = '0;
    din_master = '0;
    din_slave = '0;
    req = 2'b00;
    rst = 0;

    `ifdef RESET_ACTIVE
        repeat (5) @(posedge clk);
        req <= 2'b11;

        // No checkers, covered by AST_RST_ALL_OUTPUT_ZERO assertion
        for (int i = 0; i < TEST_ITERATION; i++) begin
            rst <= 0;
            din_master <= $urandom();
            din_slave <= $urandom();
            fork
                @(done_tx);
                @(done_rx);
            join
            repeat (5) @(posedge clk);
            rst <= 1;
            $display("%0t: RESET_ACTIVE_TEST [MONITOR] rst = %0b, dout_master = %0h, dout_slave = %0h, done_tx = %0b, done_rx = %0b", $time, rst, dout_master, dout_slave, done_tx, done_rx);
            repeat (1) @(posedge clk);
            $display("%0t: RESET_ACTIVE_TEST [MONITOR] rst = %0b, dout_master = %0h, dout_slave = %0h, done_tx = %0b, done_rx = %0b", $time, rst, dout_master, dout_slave, done_tx, done_rx);
        end

        rst <= 0;
        req <= '0;
        repeat (50) @(posedge clk);
    `endif

    `ifdef REQ_01
        for (int i = 0; i < TEST_ITERATION; i++) begin
            din_master <= $urandom();
            req <= 2'b01;
            repeat (1) @(posedge clk);
            req <= 2'b00;

            @(done_tx);
            if (dout_slave == din_master)
                $display("%0t: REQ_01 [PASS] req = 01, din_master = %0h, dout_slave = %0h", $time, din_master, dout_slave);
            else
                $display("%0t: REQ_01 [FAIL] req = 01, din_master = %0h, dout_slave = %0h", $time, din_master, dout_slave);
            repeat (10) @(posedge clk);
        end
    `endif

    `ifdef REQ_10
        for (int i = 0; i < TEST_ITERATION; i++) begin
            din_slave <= $urandom();
            req <= 2'b10;
            repeat (1) @(posedge clk);
            req <= 2'b00;

            @(done_rx);
            if (dout_master == din_slave)
                $display("%0t: REQ_10 [PASS] req = 10, din_slave = %0h, dout_master = %0h", $time, din_slave, dout_master);
            else
                $display("%0t: REQ_10 [FAIL] req = 10, din_slave = %0h, dout_master = %0h", $time, din_slave, dout_master);
            repeat (10) @(posedge clk);
        end
    `endif

    `ifdef REQ_11
        for (int i = 0; i < TEST_ITERATION; i++) begin
            din_master <= $urandom();
            din_slave <= $urandom();
            req <= 2'b11;
            repeat (1) @(posedge clk);
            req <= 2'b00;

            fork
                begin
                    @(done_rx);
                    if (dout_master == din_slave)
                        $display("%0t: REQ_11 [PASS] req = 11, din_slave = %0h, dout_master = %0h", $time, din_slave, dout_master);
                    else
                        $display("%0t: REQ_11 [FAIL] req = 11, din_slave = %0h, dout_master = %0h", $time, din_slave, dout_master);
                    end
                    begin
                    @(done_tx);
                    if (dout_slave == din_master)
                        $display("%0t: REQ_11 [PASS] req = 11, din_master = %0h, dout_slave = %0h", $time, din_master, dout_slave);
                    else
                        $display("%0t: REQ_11 [FAIL] req = 11, din_master = %0h, dout_slave = %0h", $time, din_master, dout_slave);
                end
            join
            repeat (10) @(posedge clk);
        end
    `endif

    repeat (1000) @(posedge clk);
    $finish;
end

endmodule

