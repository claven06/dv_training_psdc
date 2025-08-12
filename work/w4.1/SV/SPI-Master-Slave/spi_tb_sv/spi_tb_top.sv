module spi_tb_top;

localparam MASTER_FREQ = 100_000_000;
localparam SLAVE_FREQ = 4_000_000; // Modified from 1,800,000 to achieve spec
localparam SPI_MODE = 1;
localparam SPI_TRF_BIT = 8;

localparam TEST_ITERATION = 2;

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
typedef enum {
    NONE,
    RESET_ACTIVE,
    REQ_01,
    REQ_10,
    REQ_11
} test_t;

test_t cur_test;

// Clock generation
initial begin
    clk = 0;
    forever #5 clk= ~clk; // 100MHz clock
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

// Tasks
task reset_design;
    rst = 1;
    repeat (5) @(posedge clk);
    rst = 0;
    repeat (5) @(posedge clk);
endtask

// Main
initial begin
    wait_duration = '0;
    din_master = '0;
    din_slave = '0;
    req = 2'b00;
    rst = 0;
    cur_test <= NONE;

    repeat (5) @(posedge clk);

    `ifdef RESET_ACTIVE
        cur_test <= RESET_ACTIVE;
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
            $display("%0t: RESET_ACTIVE [MONITOR] rst = %0b, dout_master = %b, dout_slave = %b, done_tx = %0b, done_rx = %0b", $time, rst, dout_master, dout_slave, done_tx, done_rx);
            repeat (1) @(posedge clk);
            $display("%0t: RESET_ACTIVE [MONITOR] rst = %0b, dout_master = %b, dout_slave = %b, done_tx = %0b, done_rx = %0b", $time, rst, dout_master, dout_slave, done_tx, done_rx);
        end

        // Clear inputs before next test
        rst <= 0;
        req <= '0;
        din_master <= '0;
        din_slave <= '0;
        repeat (100) @(posedge clk);
    `endif

    `ifdef REQ_01
        cur_test <= REQ_01;
        for (int i = 0; i < TEST_ITERATION; i++) begin
            din_master <= $urandom();
            `ifdef WAIT_RAND
                wait_duration <= $urandom();
            `endif
            req <= 2'b01;
            #1ps $display("%0t: REQ_01 [INPUTS] req = %b, wait_duration = %0d, din_master = %b", $time, req, wait_duration, din_master);
            repeat (1) @(posedge clk);
            req <= 2'b00;

            @(done_tx);
            if (dout_slave == din_master)
                $display("%0t: REQ_01 [PASS] req = 01, din_master = %b, dout_slave = %b", $time, din_master, dout_slave);
            else
                $display("%0t: REQ_01 [FAIL] req = 01, din_master = %b, dout_slave = %b", $time, din_master, dout_slave);
            repeat (10) @(posedge clk);
        end
        // Clear inputs before next test
        din_master <= '0;
        `ifdef WAIT_RAND
            wait_duration <= '0;
        `endif
        repeat (100) @(posedge clk);
    `endif

    `ifdef REQ_10
        cur_test <= REQ_10;
        for (int i = 0; i < TEST_ITERATION; i++) begin
            din_slave <= $urandom();
            `ifdef WAIT_RAND
                wait_duration <= $urandom();
            `endif
            req <= 2'b10;
            #1ps $display("%0t: REQ_10 [INPUTS] req = %b, wait_duration = %0d, din_slave = %b", $time, req, wait_duration, din_slave);
            repeat (1) @(posedge clk);
            req <= 2'b00;

            @(done_rx);
            if (dout_master == din_slave)
                $display("%0t: REQ_10 [PASS] req = 10, din_slave = %b, dout_master = %b", $time, din_slave, dout_master);
            else
                $display("%0t: REQ_10 [FAIL] req = 10, din_slave = %b, dout_master = %b", $time, din_slave, dout_master);
            repeat (10) @(posedge clk);
        end
        // Clear inputs before next test
        din_slave <= '0;
        `ifdef WAIT_RAND
            wait_duration <= '0;
        `endif
        repeat (100) @(posedge clk);
    `endif

    `ifdef REQ_11
        cur_test <= REQ_11;
        for (int i = 0; i < TEST_ITERATION; i++) begin
            din_master <= $urandom();
            din_slave <= $urandom();
            `ifdef WAIT_RAND
                wait_duration <= $urandom();
            `endif
            req <= 2'b11;
            #1ps $display("%0t: REQ_11 [INPUTS] req = %b, wait_duration = %0d, din_master = %b, din_slave = %b", $time, req, wait_duration, din_master, din_slave);

            @(dut.spi_master_inst.state_rx == 2'b10);
            req <= '0;

            fork
                begin
                    @(done_rx);
                    if (dout_master == din_slave)
                        $display("%0t: REQ_11 S->M [PASS] req = 11, din_slave = %b, dout_master = %b", $time, din_slave, dout_master);
                    else
                        $display("%0t: REQ_11 S->M [FAIL] req = 11, din_slave = %b, dout_master = %b", $time, din_slave, dout_master);
                    end
                    begin
                    @(done_tx);
                    if (dout_slave == din_master)
                        $display("%0t: REQ_11 M->S [PASS] req = 11, din_master = %b, dout_slave = %b", $time, din_master, dout_slave);
                    else
                        $display("%0t: REQ_11 M->S [FAIL] req = 11, din_master = %b, dout_slave = %b", $time, din_master, dout_slave);
                end
            join
            repeat (10) @(posedge clk);
        end

        // Clear inputs before next test
        din_master <= '0;
        din_slave <= '0;
        `ifdef WAIT_RAND
            wait_duration <= '0;
        `endif
        repeat (100) @(posedge clk);
    `endif

    cur_test <= NONE;
    repeat (1000) @(posedge clk);
    $finish;
end

initial begin
    #100000000ps
    $finish;
end

endmodule

