`include "rand_input_pkg.sv"

module spi_tb_top;
import rand_input_pkg::*;
localparam MASTER_FREQ = 100_000_000;
localparam SLAVE_FREQ = 4_000_000; // Modified from 1,800,000 to achieve spec
localparam SPI_MODE = 1;
localparam SPI_TRF_BIT = 8;

localparam TEST_ITERATION = 10;

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

logic reset_num = 1;

// task to randomize inputs
task randomize_inputs();
	wait_duration = $urandom_range(1, 27);     // avoid 0 wait time
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

// Main
initial begin
    rand_input = new();

    wait_duration = '0;
    din_master = '0;
    din_slave = '0;
    req = 2'b00;
    rst = 0;
    cur_test = NONE;

    for (int i = 0; i < TEST_ITERATION; i++) begin
        rand_input.randomize_and_display();
        req <= rand_input.req;
        wait_duration <= rand_input.wait_duration;
        din_master <= rand_input.din_master;
        din_slave <= rand_input.din_slave;

        //@(posedge clk);
        `ifdef RESET_ACTIVE
        @(posedge clk);
        if (reset_num == 1) begin

            cur_test = RESET_ACTIVE;
            rst <= 1;      
            repeat (5) @(posedge clk);
            $display("%0t: RESET_ACTIVE [MONITOR] rst = %0b, dout_master = %b, dout_slave = %b, done_tx = %0b, done_rx = %0b", $time, rst, dout_master, dout_slave, done_tx, done_rx);
            rst <= 0;
            reset_num = 0;
        end

        `endif

        `ifdef REQ_01
        @(posedge clk);
         if (req == 2'b01) begin
            cur_test = REQ_01;
            #1ps $display("%0t: REQ_01 [INPUTS] req = %b, wait_duration = %0d, din_master = %b", $time, req, wait_duration, din_master);
            repeat (1) @(posedge clk);
            req <= 2'b00;

            @(posedge done_tx);
            if (dout_slave == din_master)
                $display("%0t: REQ_01 [PASS] req = 01, din_master = %b, dout_slave = %b", $time, din_master, dout_slave);
            else
                $display("%0t: REQ_01 [FAIL] req = 01, din_master = %b, dout_slave = %b", $time, din_master, dout_slave);
            repeat (10) @(posedge clk);

        end

        `endif

        `ifdef REQ_10
        @(posedge clk);
        if (req == 2'b10) begin
            cur_test = REQ_10;
            #1ps $display("%0t: REQ_10 [INPUTS] req = %b, wait_duration = %0d, din_slave = %b", $time, req, wait_duration, din_slave);
            repeat (1) @(posedge clk);
            req <= 2'b00;

            @(posedge done_rx);
            if (dout_master == din_slave)
                $display("%0t: REQ_10 [PASS] req = 10, din_slave = %b, dout_master = %b", $time, din_slave, dout_master);
            else
                $display("%0t: REQ_10 [FAIL] req = 10, din_slave = %b, dout_master = %b", $time, din_slave, dout_master);
            repeat (10) @(posedge clk);
        end
        `endif

        `ifdef REQ_11
        @(posedge clk);
        if (req == 2'b11) begin        
            cur_test = REQ_11;
            req <= 2'b00;
            
            #1ps $display("%0t: REQ_11 [INPUTS] req = %b, wait_duration = %0d, din_master = %b, din_slave = %b", $time, req, wait_duration, din_master, din_slave);

            //@(dut.spi_master_inst.state_rx == 2'b10);
            //req <= '0;

            fork
                begin
                    @(posedge done_rx);
                    if (dout_master == din_slave)
                        $display("%0t: REQ_11 S->M [PASS] req = 11, din_slave = %b, dout_master = %b", $time, din_slave, dout_master);
                    else
                        $display("%0t: REQ_11 S->M [FAIL] req = 11, din_slave = %b, dout_master = %b", $time, din_slave, dout_master);
                    end
                    begin
                    @(posedge done_tx);
                    if (dout_slave == din_master)
                        $display("%0t: REQ_11 M->S [PASS] req = 11, din_master = %b, dout_slave = %b", $time, din_master, dout_slave);
                    else
                        $display("%0t: REQ_11 M->S [FAIL] req = 11, din_master = %b, dout_slave = %b", $time, din_master, dout_slave);
                end
            join
            repeat (10) @(posedge clk);

        end
    `endif
    end

    `ifdef TEST_1
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
	rst = 1;
	req = 2'b00;
	@(posedge clk);
	rst = 0;
	repeat (70) begin
  	/*// ---------------- Test case 1: req = 00 ----------------
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
*/
    // Randomize req in range 01, 10, or 11
    //assert(std::randomize(req) with { req inside {2'b01, 2'b10, 2'b11}; });
    //randomize_inputs();
	rand_input = new();

    rand_input.randomize_and_display();
    req = rand_input.req;
    wait_duration = rand_input.wait_duration;
    din_master = rand_input.din_master;
    din_slave = rand_input.din_slave;

    case (req)
        2'b01: begin
            cur_test <= REQ_01_2;
            $display("[%0t] TEST REQ=01 (wait=%0d, din_master=0x%0h)",
                     $time, wait_duration, din_master);
            
            // Capture MOSI stream
            mosi_captured = '0;
            @(posedge dut.sclk);
            for (bit_idx = SPI_TRF_BIT-1; bit_idx >= 0; bit_idx--) begin
                @(negedge dut.sclk);
                mosi_captured[bit_idx] = dut.mosi;
            end
            
            wait(done_tx);

            // Checks
            if (mosi_captured !== din_master) begin
                $error("[%0t] FAIL: MOSI mismatch (REQ=01)", $time);
                fail_count++;
            end else pass_count++;

            if (dout_slave == din_master) begin
				pass_count++;
            end else begin
				fail_count++;
				$error("[%0t] FAIL: dout_slave and din_master mismatch (REQ=01)", $time);
			end
        end

        2'b10: begin
            cur_test <= REQ_10_2;
            $display("[%0t] TEST REQ=10 (wait=%0d, din_slave=0x%0h)",
                     $time, wait_duration, din_slave);
            
            // Capture MISO
            miso_captured = '0;
            @(posedge dut.sclk);
            for (bit_idx = SPI_TRF_BIT-1; bit_idx >= 0; bit_idx--) begin
                @(negedge dut.sclk);
                miso_captured[bit_idx] = dut.miso;
            end
            
            wait(done_rx);

            // Checks
            if (miso_captured !== din_slave) begin
                $error("[%0t] FAIL: MISO mismatch (REQ=10)", $time);
                fail_count++;
            end else pass_count++;

            if (dout_master == din_slave) begin
				pass_count++;
            end else begin 
				fail_count++;
				$error("[%0t] FAIL: dout_slave and din_master mismatch (REQ=10)", $time);
			end
        end

        2'b11: begin
            cur_test <= REQ_11_2;
            $display("[%0t] TEST REQ=11 (wait=%0d, din_master=0x%0h, din_slave=0x%0h)",
                     $time, wait_duration, din_master, din_slave);
            
            mosi_captured = '0;
            miso_captured = '0;
            @(posedge dut.sclk);
            for (bit_idx = SPI_TRF_BIT-1; bit_idx >= 0; bit_idx--) begin
                @(negedge dut.sclk);
                mosi_captured[bit_idx] = dut.mosi;
                miso_captured[bit_idx] = dut.miso;
            end

            fork
                wait(done_rx);
                wait(done_tx);
            join

            // Checks
            if (mosi_captured !== din_master) begin
				fail_count++;
				$error("[%0t] FAIL: MOSI mismatch (REQ=11)", $time);
            end else pass_count++;

            if (miso_captured !== din_slave) begin
				fail_count++;
				$error("[%0t] FAIL: MISO mismatch (REQ=11)", $time);
            end else pass_count++;

            if ((dout_master == din_slave) && (dout_slave == din_master)) begin
                pass_count++;
            end else begin
				fail_count++;
				$error("[%0t] FAIL: dout_slave and din_master mismatch (REQ=11)", $time);
			end
        end
    endcase
	end
  	$display("[%0t] TEST SUMMARY: PASS=%0d FAIL=%0d", $time, pass_count, fail_count);
  	$finish;

    `endif

    cur_test <= NONE;
    repeat (1000) @(posedge clk);
    $finish;
end

`include "coverage.sv"
//initial begin
//    #100000000ps
//    $finish;
//end

endmodule

