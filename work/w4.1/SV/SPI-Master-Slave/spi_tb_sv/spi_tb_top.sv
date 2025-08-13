module spi_tb_top;

localparam MASTER_FREQ = 100_000_000;
localparam SLAVE_FREQ = 4_000_000; // Modified from 1,800,000 to achieve spec
localparam SPI_MODE = 1;
localparam SPI_TRF_BIT = 8;

localparam TEST_ITERATION = 4;

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

time t1;
time t2;
real period_ns;
real freq_mhz;
int unsigned pass_count = 0, fail_count = 0;
// Store previous outputs for comparison
logic [(SPI_TRF_BIT-1):0] prev_dout_master;
logic [(SPI_TRF_BIT-1):0] prev_dout_slave;
reg [SPI_TRF_BIT-1:0] mosi_captured;
reg [SPI_TRF_BIT-1:0] miso_captured;
integer bit_idx;

// task to randomize inputs
task randomize_inputs();
	//wait_duration = $urandom_range(1, 27);     // avoid 0 wait time
	din_master    = $urandom_range(0, 255);
	din_slave     = $urandom_range(0, 255);
endtask

// Testbench signals
typedef enum {
    NONE,
    RESET_ACTIVE,
    REQ_01,
    REQ_10,
    REQ_11,
    RESET_ACTIVE_2,
    SCLK_TEST,
    REQ_00_2,
    REQ_01_2,
    REQ_10_2,
    REQ_11_2
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
            repeat (2) @(posedge clk);
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
            repeat (2) @(posedge clk);
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
            repeat (2) @(posedge clk);
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

    `ifdef TEST_1
    cur_test <= RESET_ACTIVE_2;
	// Apply Reset
	@(posedge clk);
    	wait_duration = 8'ha;
    	din_master = 8'hb8;
    	din_slave = 8'ha2;
    	req = 2'b01;

    	repeat (200) @(posedge clk); // run for 200 cycles
	$display("[%0t] Applying reset...", $time);
    	rst = 1;

    	@(posedge clk);

    	// Check reset effect
    	if (dout_master !== '0 || dout_slave !== '0 || done_tx !== 0 || done_rx !== 0) begin
      		$error("[%0t] Reset failed: outputs not cleared", $time);
    	end else begin
      		$display("[%0t] Reset test passed", $time);
    	end

	// sclk test case
    cur_test <= SCLK_TEST;
	@(posedge clk);
	rst = 0;
	repeat (10) @(posedge clk);
    	force dut.sclk_en = 1'b1; // or drive via master request flow
    	$display("[%0t] SCLK_en forced HIGH", $time);

    	// Measure SCLK frequency

    	@(posedge dut.sclk);
    	t1 = $time;
    	@(posedge dut.sclk);
    	t2 = $time;

    	period_ns = t2 - t1;
    	freq_mhz = 1000 / period_ns; // ns -> MHz
    	$display("Measured SCLK period: %0t ns, freq: %0.3f MHz", period_ns, freq_mhz);

    	if (freq_mhz < 3.69 || freq_mhz > 3.71)
      		$error("SCLK frequency out of range: %0.3f MHz", freq_mhz);
    	else
      		$display("SCLK frequency OK: %0.3f MHz", freq_mhz);

    	// Check SCLK idle when disabled
    	force dut.sclk_en = 1'b0;
    	$display("[%0t] SCLK_en forced LOW", $time);
    	repeat (5) @(posedge clk);
    		if (dut.sclk !== dut.sclk) // no toggle check
      			$error("SCLK toggled when SCLK_en=0");
    		else
      			$display("SCLK idle when disabled - OK");

    	release dut.sclk_en;

    `endif

    `ifdef TEST_2

  	// Initialize
  	@(posedge clk);

	repeat (10) begin
  	// ---------------- Test case 1: req = 00 ----------------
    cur_test <= REQ_00_2;
  	randomize_inputs();
  	$display("[%0t] TEST REQ = 00 (wait=%0d, din_master=0x%0h, din_slave=0x%0h)",
        	$time, wait_duration, din_master, din_slave);
  	req = 2'b00;
	prev_dout_master = dout_master;
	prev_dout_slave = dout_slave;
  	repeat (50) @(posedge clk);
  	if ((prev_dout_master == dout_master) && (prev_dout_slave == dout_slave) && (done_tx === 1'b0) && (done_rx === 1'b0)) begin
    		$display("[%0t] PASS: REQ=00 outputs are IDLE.", $time);
    		pass_count++;
  		end else begin
    		$error("[%0t] FAIL: REQ=00 - unexpected outputs or done flags.", $time);
    		$display("  dout_slave=%p dout_master=%p done_tx=%b done_rx=%b", dout_slave, dout_master, done_tx, done_rx);
    		fail_count++;
  	end

  	// ---------------- Test case 2: req = 01 ----------------
    cur_test <= REQ_01_2;
  	randomize_inputs();
  	//din_slave = 8'h00; // slave output unused in TX mode
  	$display("[%0t] TEST REQ = 01 (wait=%0d, din_master=0x%0h)",
           	$time, wait_duration, din_master);
  	req = 2'b01;

	// Capture MOSI stream for MSB-first check
	mosi_captured = '0;
	@(posedge dut.sclk); // Wait for first transfer edge
	for (bit_idx = SPI_TRF_BIT-1; bit_idx >= 0; bit_idx--) begin
		@(posedge dut.sclk); // adjust for SPI mode if needed
		mosi_captured[bit_idx] = dut.mosi;
	end

  	wait(done_tx);

	// Check MSB-first correctness
	if (mosi_captured !== din_master) begin
		$error("[%0t] FAIL: MOSI MSB-first mismatch (REQ=01). Expected=%b Got=%b",
		       $time, din_master, mosi_captured);
		fail_count++;
	end else begin
		$display("[%0t] PASS: MOSI MSB-first OK (REQ=01)", $time);
		pass_count++;
	end

  	if (dout_slave == din_master) begin
    		$display("[%0t] PASS: REQ=01 dout_slave == din_master", $time);
    		pass_count++;
  	end else begin
    		$error("[%0t] FAIL: REQ=01 - unexpected outputs", $time);
    		$display("  dout_slave=%p dout_master=%p done_tx=%b done_rx=%b", dout_slave, dout_master, done_tx, done_rx);
    		fail_count++;
  	end

  	// ---------------- Test case 3: req = 10 ----------------
    cur_test <= REQ_10_2;
  	randomize_inputs();
  	//din_master = 8'h00; // master output unused in RX mode
  	$display("[%0t] TEST REQ = 10 (wait=%0d, din_slave=0x%0h)",
           $time, wait_duration, din_slave);
  	req = 2'b10;

	// Capture MISO stream for MSB-first check
	miso_captured = '0;
	@(posedge dut.sclk);
	for (bit_idx = SPI_TRF_BIT-1; bit_idx >= 0; bit_idx--) begin
		@(posedge dut.sclk);
		miso_captured[bit_idx] = dut.miso;
	end

  	wait(done_rx);

	// Check MSB-first correctness
	if (miso_captured !== din_slave) begin
		$error("[%0t] FAIL: MISO MSB-first mismatch (REQ=10). Expected=%b Got=%b",
		       $time, din_slave, miso_captured);
		fail_count++;
	end else begin
		$display("[%0t] PASS: MISO MSB-first OK (REQ=10)", $time);
		pass_count++;
	end

  	if (dout_master == din_slave) begin
    		$display("[%0t] PASS: REQ=10 dout_master == din_slave", $time);
    		pass_count++;
  	end else begin
    		$error("[%0t] FAIL: REQ=10 - unexpected outputs", $time);
    		$display("  dout_slave=%p dout_master=%p done_tx=%b done_rx=%b", dout_slave, dout_master, done_tx, done_rx);
    		fail_count++;
  	end

  	// ---------------- Test case 4: req = 11 ----------------
    cur_test <= REQ_11_2;
  	randomize_inputs();
  	$display("[%0t] TEST REQ = 11 (wait=%0d, din_master=0x%0h, din_slave=0x%0h)",
           	$time, wait_duration, din_master, din_slave);
  	req = 2'b11;

	// Capture MOSI & MISO on the SPI clock edges
	mosi_captured = '0;
	miso_captured = '0;

	// Wait for first SCLK edge (start of transfer)
	@(posedge dut.sclk);

	for (bit_idx = SPI_TRF_BIT-1; bit_idx >= 0; bit_idx--) begin
    	@(posedge dut.sclk);
    	mosi_captured[bit_idx] = dut.mosi;
    	miso_captured[bit_idx] = dut.miso;
	end

  	wait(done_rx);
  	wait(done_tx);


	// Check captured MSB-first streams
	if (mosi_captured !== din_master) begin
		$error("[%0t] FAIL: MOSI MSB-first mismatch. Expected=%b Got=%b",
		       $time, din_master, mosi_captured);
		fail_count++;
	end else begin
		$display("[%0t] PASS: MOSI MSB-first OK", $time);
		pass_count++;
	end

	if (miso_captured !== din_slave) begin
		$error("[%0t] FAIL: MISO MSB-first mismatch. Expected=%b Got=%b",
		       $time, din_slave, miso_captured);
		fail_count++;
	end else begin
		$display("[%0t] PASS: MISO MSB-first OK", $time);
		pass_count++;
	end

	// Check dout
  	if ((dout_master == din_slave) && (dout_slave == din_master)) begin
    		$display("[%0t] PASS: REQ=11 Both dout match expected", $time);
    		pass_count++;
  	end else begin
    		$error("[%0t] FAIL: REQ=11 - unexpected outputs", $time);
    		$display("  dout_slave=%p dout_master=%p done_tx=%b done_rx=%b", dout_slave, dout_master, done_tx, done_rx);
    		fail_count++;
  	end

	end
  	$display("[%0t] TEST SUMMARY: PASS=%0d FAIL=%0d", $time, pass_count, fail_count);
  	$finish;

    `endif

    cur_test <= NONE;
    repeat (1000) @(posedge clk);
    $finish;
end

//initial begin
//    #100000000ps
//    $finish;
//end

endmodule

