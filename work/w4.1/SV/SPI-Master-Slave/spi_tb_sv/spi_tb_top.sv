`include "rand_input_pkg.sv"

module spi_tb_top;
import rand_input_pkg::*;
localparam MASTER_FREQ = 100_000_000;
localparam SLAVE_FREQ = 5_000_000; // Modified from 1,800,000 to achieve spec
localparam SPI_MODE = 1;
localparam SPI_TRF_BIT = 8;

localparam TEST_ITERATION = 1000;

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

time t1, t2;
real period_ns;
real freq_mhz;
int unsigned pass_count = 0, fail_count = 0;
// Store previous outputs for comparison
reg [SPI_TRF_BIT-1:0] mosi_captured;
reg [SPI_TRF_BIT-1:0] miso_captured;
int bit_idx;

logic reset_num = 1;
logic prev_sclk = 0;
bit [1:0] prev_req;
logic [(SPI_TRF_BIT-1):0] prev_dout_master;
logic [(SPI_TRF_BIT-1):0] prev_dout_slave;
int sclk_posedge_count, sclk_negedge_count;

// Testbench signals
typedef enum {
    NONE,
    FIRST_RESET,
    REQ_01,
    REQ_10,
    REQ_11,
    RESET_ACTIVE_TEST,
    SCLK_TEST,
    RESET_ACTIVE_B2B,
    REQ_00_B2B,
    REQ_01_B2B,
    REQ_10_B2B,
    REQ_11_B2B,
	WAIT_STATE_1_to_IDLE
} test_t;

test_t cur_test;
Rand_Input rand_input;

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

// Coverages
`include "coverage.sv"

// Sampling previous sclk
always @(posedge clk) begin
    prev_sclk <= dut.sclk;
end

// Reset previous values when reset asserted
always @(posedge rst) begin
    prev_req <= 2'b00;
    prev_dout_master <= '0;
    prev_dout_slave <= '0;
end

// Count exact number of posedges and negedges of sclk
always @(posedge clk or posedge rst) begin
    if (rst) begin
        sclk_posedge_count <= 0;
    end
    else begin
        if (dut.sclk_en) begin
            if (dut.spi_master_inst.sclk_posedge) begin
                sclk_posedge_count <= sclk_posedge_count + 1;
            end
        end else begin
            if (sclk_posedge_count != 0 && sclk_posedge_count != SPI_TRF_BIT) begin
                $error("%0t: SCLK_COUNT_TEST [FAIL] sclk had %0d POS-edges when sclk_en asserted (expected %0d)", $time, sclk_posedge_count, SPI_TRF_BIT);
            end
            #1ps
            sclk_posedge_count <= 0;
        end
    end
end

always @(posedge clk or posedge rst) begin
    if (rst) begin
        sclk_negedge_count <= 0;
    end
    else begin
        if (dut.sclk_en) begin
            if (dut.spi_master_inst.sclk_negedge) begin
                sclk_negedge_count <= sclk_negedge_count + 1;
            end
        end else begin
            if (sclk_negedge_count != 0 && sclk_negedge_count != SPI_TRF_BIT) begin
                $error("%0t: SCLK_COUNT_TEST [FAIL] sclk had %0d NEG-edges when sclk_en asserted (expected %0d)", $time, sclk_negedge_count, SPI_TRF_BIT);
            end
            #1ps
            sclk_negedge_count <= 0;
        end
    end
end

// Main
initial begin
    cur_test <= NONE;
    rand_input = new();

    wait_duration = '0;
    din_master = '0;
    din_slave = '0;
    req = 2'b00;
    rst = 0;
    pass_count = 0;
    fail_count = 0;

    `ifdef RESET_ACTIVE_TEST
        cur_test <= RESET_ACTIVE_TEST;
        // Set inputs
    	wait_duration <= 8'ha;
    	din_master <= 8'hb8;
    	din_slave <= 8'ha2;
    	req <= 2'b11;

        // Run for 200 cycles to let outputs stable
    	repeat (200) @(posedge clk);

        // Assert reset
    	rst <= 1;
	    #1ps $display("%0t: RESET_ACTIVE_TEST [INPUTS] rst = %0b, req = %0b, wait_duration = %d, din_master = %b, din_slave = %b", $time, rst, req, wait_duration, din_master, din_slave);

        // Check reset effect for 20 cycles
        repeat (20) begin
            if (dout_master !== '0 || dout_slave !== '0 || done_tx !== 0 || done_rx !== 0) begin
                $error("%0t: RESET_ACTIVE_TEST [FAIL] dout_master = %b, dout_slave = %b, done_tx = %0b, done_rx = %0b", $time, dout_master, dout_slave, done_tx, done_rx);
                fail_count++;
            end else begin
                $display("%0t: RESET_ACTIVE_TEST [PASS] dout_master = %b, dout_slave = %b, done_tx = %0b, done_rx = %0b", $time, dout_master, dout_slave, done_tx, done_rx);
                pass_count++;
            end
            repeat (1) @(posedge clk);
        end
        rst <= 0;
        repeat (10) @(posedge clk);
    `endif

    $display("[%0t] RESET_ACTIVE_TEST SUMMARY: PASS=%0d FAIL=%0d", $time, pass_count, fail_count);

    pass_count = 0;
    fail_count = 0;

    `ifdef SCLK_TEST
        cur_test <= SCLK_TEST;
        rst <= 0;
    	req <= 2'b00;
        repeat (20) @(posedge clk);
        force dut.sclk_en = 1'b1; // or drive via master request flow
        $display("%0t: SCLK_TEST [INPUTS] sclk_en (%0b) forced HIGH", $time, dut.sclk_en);

        // Measure SCLK frequency
        @(posedge dut.sclk);
        t1 = $time;
        @(posedge dut.sclk);
        t2 = $time;

        period_ns = t2 - t1;
        freq_mhz = 1000 / period_ns; // ns -> MHz
        $display("%0t: SCLK_TEST [MONITOR] Measured SCLK period: %0t ns, freq: %0.3f MHz", $time, period_ns, freq_mhz);

        if (freq_mhz < ((SLAVE_FREQ / 1000000.00) - 0.01) || freq_mhz > ((SLAVE_FREQ / 1000000.00) + 0.01)) begin
            $error("%0t: SCLK_TEST [FAIL] SCLK frequency out of range at %0.3f MHz (expect %0.3f MHz)", $time, freq_mhz, (SLAVE_FREQ / 1000000.00 ));
            fail_count++;
        end
        else begin
            $display("%0t: SCLK_TEST [PASS] SCLK frequency expected at %0.3f MHz", $time, freq_mhz);
            pass_count++;
        end

        repeat (SPI_TRF_BIT - 2) @(posedge dut.sclk);

        // Check SCLK idle when disabled
        force dut.sclk_en = 1'b0;
        repeat (5) @(posedge clk);

        $display("%0t: SCLK_TEST [INPUTS] sclk_en (%0b) forced LOW", $time, dut.sclk_en);

        // Check for the maximum number of counter in clock divider
        repeat (1024) begin
            repeat (1) @(posedge clk);
            if (dut.sclk !== prev_sclk) begin // No toggle check
                $error("%0t: SCLK_TEST [FAIL] sclk = %0b, prev_sclk = %0b", $time, dut.sclk, prev_sclk);
                fail_count++;
            end
            else begin
                $display("%0t: SCLK_TEST [PASS] SCLK remained idle when sclk_en = %0b", $time, dut.sclk_en);
                pass_count++;
            end
        end

        release dut.sclk_en;
        rst <= 1;
        req <= 2'b00;
        repeat (10) @(posedge clk)
        rst <= 0;
    `endif

    $display("[%0t] SCLK_TEST SUMMARY: PASS=%0d FAIL=%0d", $time, pass_count, fail_count);

    pass_count = 0;
    fail_count = 0;

    for (int i = 0; i < TEST_ITERATION; i++) begin
        rand_input.randomize_and_display();
        req <= rand_input.req;
        wait_duration <= rand_input.wait_duration;
        din_master <= rand_input.din_master;
        din_slave <= rand_input.din_slave;

        #1ps

        fork
            `ifdef REQ_01
                if (req == 2'b01) begin
                    cur_test <= REQ_01;
                    #1ps $display("%0t: REQ_01 [INPUTS] req = %b, wait_duration = %0d, din_master = %b", $time, req, wait_duration, din_master);
                    repeat (2) @(posedge clk);
                    req <= 2'b00;

                    @(posedge done_tx);
                    if (dout_slave == din_master) begin
                        $display("%0t: REQ_01 [PASS] req = 01, din_master = %b, dout_slave = %b", $time, din_master, dout_slave);
                        pass_count++;
                    end
                    else begin
                        $error("%0t: REQ_01 [FAIL] req = 01, din_master = %b, dout_slave = %b", $time, din_master, dout_slave);
                        fail_count++;
                    end
                    repeat (10) @(posedge clk);
                end
            `endif

            `ifdef REQ_10
                if (req == 2'b10) begin
                    cur_test <= REQ_10;
                    #1ps $display("%0t: REQ_10 [INPUTS] req = %b, wait_duration = %0d, din_slave = %b", $time, req, wait_duration, din_slave);
                    repeat (2) @(posedge clk);
                    req <= 2'b00;

                    @(posedge done_rx);
                    if (dout_master == din_slave) begin
                        $display("%0t: REQ_10 [PASS] req = 10, din_slave = %b, dout_master = %b", $time, din_slave, dout_master);
                        pass_count++;
                    end
                    else begin
                        $error("%0t: REQ_10 [FAIL] req = 10, din_slave = %b, dout_master = %b", $time, din_slave, dout_master);
                        fail_count++;
                    end
                    repeat (10) @(posedge clk);
                end
            `endif

            `ifdef REQ_11
                if (req == 2'b11) begin
                    cur_test <= REQ_11;
                    #1ps $display("%0t: REQ_11 [INPUTS] req = %b, wait_duration = %0d, din_master = %b, din_slave = %b", $time, req, wait_duration, din_master, din_slave);
                    repeat (2) @(posedge clk);
                    req <= 2'b00;

                    fork
                        begin
                            @(posedge done_rx);
                            if (dout_master == din_slave) begin
                                $display("%0t: REQ_11 S->M [PASS] req = 11, din_slave = %b, dout_master = %b", $time, din_slave, dout_master);
                                pass_count++;
                            end
                            else begin
                                $error("%0t: REQ_11 S->M [FAIL] req = 11, din_slave = %b, dout_master = %b", $time, din_slave, dout_master);
                                fail_count++;
                            end
                        end
                        begin
                            @(posedge done_tx);
                            if (dout_slave == din_master) begin
                                $display("%0t: REQ_11 M->S [PASS] req = 11, din_master = %b, dout_slave = %b", $time, din_master, dout_slave);
                                pass_count++;
                            end
                            else begin
                                $error("%0t: REQ_11 M->S [FAIL] req = 11, din_master = %b, dout_slave = %b", $time, din_master, dout_slave);
                                fail_count++;
                            end
                        end
                    join
                    repeat (10) @(posedge clk);
                end
            `endif
        join
    end

    $display("[%0t] PULSE_REQ TESTS SUMMARY: PASS=%0d FAIL=%0d", $time, pass_count, fail_count);

    pass_count = 0;
    fail_count = 0;

    // Reset the design for back to back operation
    rst <= 1;
    req <= 2'b00;
    prev_req <= 2'b00;
    prev_dout_master <= '0;
    prev_dout_slave <= '0;
    repeat (10) @(posedge clk)
    rst <= 0;

    repeat (TEST_ITERATION) begin
        rst <= rand_input.rst;
        req <= rand_input.req;
        wait_duration <= rand_input.wait_duration;
        din_master <= rand_input.din_master;
        din_slave <= rand_input.din_slave;
        mosi_captured <= '0;
        miso_captured <= '0;
        rand_input.randomize_and_display();

        #1ps
        `ifdef RESET_ACTIVE_B2B
            // If reset is asserted, check all outputs immediately
            if (rst) begin
                if ((dout_master !== '0) || (dout_slave !== '0) || (done_tx !== '0) || (done_rx !== '0)) begin
                    $error("%0t: RESET_ACTIVE_B2B [FAIL] dout_master = %b, dout_slave = %b, done_tx = %0b, done_rx = %0b", $time, dout_master, dout_slave, done_tx, done_rx);
                    fail_count++;
                end else begin
                    pass_count++;
                    $display("%0t: RESET_ACTIVE_B2B [PASS] dout_master = %b, dout_slave = %b, done_tx = %0b, done_rx = %0b", $time, dout_master, dout_slave, done_tx, done_rx);
                end

                repeat (5) @(posedge clk);
                continue; // Skip SPI transfer for this cycle
            end
        `endif

        `ifdef REQ_01_B2B
            if (req == 2'b01) begin
                cur_test <= REQ_01_B2B;
                $display("%0t: REQ_01_B2B [INPUTS] req = %b, wait_duration = %0d, din_master = %b", $time, req, wait_duration, din_master);

                // Capture MOSI stream
                for (bit_idx = (SPI_TRF_BIT-1); bit_idx >= 0; bit_idx--) begin
                    repeat (1) @(negedge dut.sclk);
                    mosi_captured[bit_idx] <= dut.mosi;
                end

                @(posedge done_tx);

                // Checks
                #1ps
                if (mosi_captured == din_master) begin
                    $display("%0t: REQ_01_B2B MSB_FIRST [PASS] req = %b, din_master = %b, mosi_captured = %b", $time, req, din_master, mosi_captured);
                    pass_count++;
                end
                else begin
                    $error("%0t: REQ_01_B2B MSB_FIRST [FAIL] req = %b, din_master = %b, mosi_captured = %b", $time, req, din_master, mosi_captured);
                    fail_count++;
                end

                if (dout_slave == din_master) begin
                    $display("%0t: REQ_01_B2B [PASS] req = %b, din_master = %b, dout_slave = %b", $time, req, din_master, dout_slave);
                    pass_count++;
                end
                else begin
                    $error("%0t: REQ_01_B2B [FAIL] req = %b, din_master = %b, dout_slave = %b", $time, req, din_master, dout_slave);
                    fail_count++;
                end
            end
        `endif

        `ifdef REQ_10_B2B
            if (req == 2'b10) begin
                cur_test <= REQ_10_B2B;
                $display("%0t: REQ_10_B2B [INPUTS] req = %b, wait_duration = %0d, din_slave = %b", $time, req, wait_duration, din_slave);

                // Capture MISO stream
                for (bit_idx = (SPI_TRF_BIT-1); bit_idx >= 0; bit_idx--) begin
                    repeat (1) @(negedge dut.sclk);
                    miso_captured[bit_idx] <= dut.miso;
                end

                @(posedge done_rx);

                // Checks
                #1ps
                if (miso_captured == din_slave) begin
                    $display("%0t: REQ_10_B2B MSB_FIRST [PASS] req = %b, din_slave = %b, miso_captured = %b", $time, req, din_slave, miso_captured);
                    pass_count++;
                end
                else begin
                    $error("%0t: REQ_10_B2B MSB_FIRST [FAIL] req = %b, din_slave = %b, miso_captured = %b", $time, req, din_slave, miso_captured);
                    fail_count++;
                end

                if (dout_master == din_slave) begin
                    $display("%0t: REQ_10_B2B [PASS] req = %b, din_slave = %b, dout_master = %b", $time, req, din_slave, dout_master);
                    pass_count++;
                end
                else begin
                    $error("%0t: REQ_10_B2B [FAIL] req = %b, din_slave = %b, dout_master = %b", $time, req, din_slave, dout_master);
                    fail_count++;
                end
            end
        `endif

        `ifdef REQ_11_B2B
            if (req == 2'b11) begin
                cur_test <= REQ_11_B2B;
                $display("%0t: REQ_11_B2B [INPUTS] req = %b, wait_duration = %0d, din_master = %b, din_slave = %b", $time, req, wait_duration, din_master, din_slave);

                // Capture MOSI/MISO stream
                for (bit_idx = (SPI_TRF_BIT-1); bit_idx >= 0; bit_idx--) begin
                    repeat (1) @(negedge dut.sclk);
                    mosi_captured[bit_idx] <= dut.mosi;
                    miso_captured[bit_idx] <= dut.miso;
                end

                fork
                    begin
                        @(posedge done_rx);
                        #1ps
                        if (mosi_captured == din_master) begin
                            $display("%0t: REQ_11_B2B MSB_FIRST [PASS] req = %b, din_master = %b, mosi_captured = %b", $time, req, din_master, mosi_captured);
                            pass_count++;
                        end
                        else begin
                            $error("%0t: REQ_11_B2B MSB_FIRST [FAIL] req = %b, din_master = %b, mosi_captured = %b", $time, req, din_master, mosi_captured);
                            fail_count++;
                        end

                        if (dout_slave == din_master) begin
                            $display("%0t: REQ_11_B2B [PASS] req = %b, din_master = %b, dout_slave = %b", $time, req, din_master, dout_slave);
                            pass_count++;
                        end
                        else begin
                            $error("%0t: REQ_11_B2B [FAIL] req = %b, din_master = %b, dout_slave = %b", $time, req, din_master, dout_slave);
                            fail_count++;
                        end
                    end
                    begin
                        @(posedge done_tx);
                        #1ps
                        if (miso_captured == din_slave) begin
                            $display("%0t: REQ_11_B2B MSB_FIRST [PASS] req = %b, din_slave = %b, miso_captured = %b", $time, req, din_slave, miso_captured);
                            pass_count++;
                        end
                        else begin
                            $error("%0t: REQ_11_B2B MSB_FIRST [FAIL] req = %b, din_slave = %b, miso_captured = %b", $time, req, din_slave, miso_captured);
                            fail_count++;
                        end

                        if (dout_master == din_slave) begin
                            $display("%0t: REQ_11_B2B [PASS] req = %b, din_slave = %b, dout_master = %b", $time, req, din_slave, dout_master);
                            pass_count++;
                        end
                        else begin
                            $error("%0t: REQ_11_B2B [FAIL] req = %b, din_slave = %b, dout_master = %b", $time, req, din_slave, dout_master);
                            fail_count++;
                        end
                    end
                join
            end
        `endif

        `ifdef REQ_00_B2B
            if (req == 2'b00) begin
                cur_test <= REQ_00_B2B;
                $display("%0t: REQ_00_B2B [INPUTS] req = %b, wait_duration = %0d, din_master = %b, din_slave = %b", $time, req, wait_duration, din_master, din_slave);

                // Idle: check outputs match the last transfer
                if (dout_master == prev_dout_master) begin
                    $display("%0t REQ_00_B2B [PASS] req = %b, prev_req = %b, dout_master = %b, prev_dout_master = %b", $time, req, prev_req, dout_master, prev_dout_master);
                    pass_count++;
                end
                else begin
                    $error("%0t REQ_00_B2B [FAIL] req = %b, prev_req = %b, dout_master = %b, prev_dout_master = %b", $time, req, prev_req, dout_master, prev_dout_master);
                    fail_count++;
                end

                if (dout_slave == prev_dout_slave) begin
                    $display("%0t REQ_00_B2B [PASS] req = %b, prev_req = %b, dout_slave = %b, prev_dout_slave = %b", $time, req, prev_req, dout_slave, prev_dout_slave);
                    pass_count++;
                end
                else begin
                    $error("%0t REQ_00_B2B [FAIL] req = %b, prev_req = %b, dout_slave = %b, prev_dout_slave = %b", $time, req, prev_req, dout_slave, prev_dout_slave);
                    fail_count++;
                end
            end
        `endif


        // Store previous cycle values
        prev_req <= req;
        prev_dout_slave <= dout_slave;
        prev_dout_master <= dout_master;
    end
    $display("[%0t] B2B TESTS SUMMARY: PASS=%0d FAIL=%0d", $time, pass_count, fail_count);

	`ifdef WAIT_STATE_1_to_IDLE
		cur_test <= WAIT_STATE_1_to_IDLE;
		rst <= 1;
		req <= 2'b00;
		repeat (10) @(posedge clk)
		rst <= 0;
        din_master <= 8'ha5;

		req <= 2'b01;
		@(dut.spi_master_inst.state_tx == 2'b01);
		if (dut.spi_master_inst.state_tx == 2'b01) begin
			
            $display("%0t: WAIT_STATE_1_to_IDLE [INPUTS] req = %b, wait_duration = %0d, din_master = %b, din_slave = %b", $time, req, wait_duration, din_master, din_slave);
			@(posedge clk);
			rst <= 1;
			#1ps
			if (dut.spi_master_inst.state_tx == 2'b00) begin
				$display("%0t: WAIT_STATE_1_to_IDLE [PASS] req = %b, wait_duration = %0d, din_master = %b, din_slave = %b", $time, req, wait_duration, din_master, din_slave);
				pass_count++;
			end else begin
				$display("%0t: WAIT_STATE_1_to_IDLE [FAIL] req = %b, wait_duration = %0d, din_master = %b, din_slave = %b", $time, req, wait_duration, din_master, din_slave);
				fail_count++;
			end
		end	else $display("Not found");	

	`endif
	$display("[%0t] WAIT_STATE_1_to_IDLE TESTS SUMMARY: PASS=%0d FAIL=%0d", $time, pass_count, fail_count);

    cur_test <= NONE;
    repeat (1000) @(posedge clk);
    $finish;
end


endmodule

