`timescale 1ns/1ps

module tb_top;

// DUT signals
logic 		clk;
logic 		rstn;
logic 		vld;
logic [7:0] addr;
logic [7:0] data;
logic [7:0] addr_a;
logic [7:0] data_a;
logic [7:0] addr_b;
logic [7:0] data_b;

// Clock
initial begin
    clk <= '0;
    forever begin
        #10 clk <= ~clk; // 20ns period = 50 MHz clock
    end
end

// DUT instantiation
bus_switching_controller #(
) DUT (
    .*
);

// Dump waveform in FSDB
initial begin
  $fsdbDumpfile("dump.fsdb");
  $fsdbDumpvars(0, tb_top);
  $fsdbDumpMDA();
  $fsdbDumpSVA();
end

// Assertions
AST_RESET_ZERO_CHECK: assert property (@(posedge clk) (!rstn) |-> (data_a == '0) && (addr_a == '0) && (data_b == '0) && (addr_b == '0))
    else $error("-E- AST_RESET_ZERO_CHECK failed at %0t, rstn (%0h) data_a (%0h) addr_a (%0h) data_b (%0h) addr_b (%0h)", $time, data_a, addr_a, data_b, addr_b);

AST_VLD_ZERO_CHECK: assert property (@(posedge clk) disable iff (!rstn) vld |-> ##1 ((data_a == $past(data)) || (data_b == $past(data))) && ((addr_a == $past(addr)) || (addr_b == $past(addr))))
    else $error("-E- AST_VLD_PIPELINE_CHECK failed at %0t, data 1 cycle before (%0h), data_a (%0h), data_b (%0h), addr 1 cycle before (%0h), addr_a (%0h), addr_b (%0h)", $time, $past(data), data_a, data_b, $past(addr), addr_a, addr_b);

AST_CHOOSE_A_PORTS_CHECK: assert property (@(posedge clk) disable iff (!rstn) (vld && addr < 8'40) |-> ##1 (data_a == $past(data)) && (addr_a == $past(addr)) && (data_b == '0) && (addr_b == '0))
    else $error("-E- AST_CHOOSE_A_PORTS_CHECK failed at %0t, data 1 cycle before (%0h), data_a (%0h), data_b (%0h), addr 1 cycle before (%0h), addr_a (%0h), addr_b (%0h)", $time, $past(data), data_a, data_b, $past(addr), addr_a, addr_b)

AST_CHOOSE_B_PORTS_CHECK: assert property (@(posedge clk) disable iff (!rstn) (vld && addr >= 8'40) |-> ##1 (data_b == $past(data)) && (addr_b == $past(addr)) && (data_a == '0) && (addr_a == '0))
    else $error("-E- AST_CHOOSE_B_PORTS_CHECK failed at %0t, data 1 cycle before (%0h), data_a (%0h), data_b (%0h), addr 1 cycle before (%0h), addr_a (%0h), addr_b (%0h)", $time, $past(data), data_a, data_b, $past(addr), addr_a, addr_b)

// Main
initial begin
    // Initialize inputs to '0, assert active low reset
    rstn    <= '0;
    vld     <= '0;
    data    <= '0;
    addr    <= '0;

    repeat(10) @(posedge clk);

    `ifdef RESET_TEST
    for (int i = 0; i < ITER_NUM; i++) begin
        addr <= $urandom();
        data <= $urandom();

        repeat(5) @(posedge clk);
    end
    repeat(10) @(posedge clk);
    `endif

    // Out of reset
    repeat(1) @(negedge clk);
    rstn    <= 1'b1;

    `ifdef VALID_TEST
    // Valid = 0, expect outputs to remain 0
    vld <= '0;
    for (int i = 0; i < ITER_NUM; i++) begin
        addr <= $urandom();
        data <= $urandom();

        repeat(5) @(posedge clk);
    end

    // Valid = 1, expect either A or B outputs to have values
    vld <= 1'b1;
    for (int i = 0; i < ITER_NUM; i++) begin
        addr <= $urandom();
        data <= $urandom();

        repeat(5) @(posedge clk);
    end

    // Deassert valid
    vld <= '0;
    repeat(10) @(posedge clk);
    `endif

    `ifdef DATA_TEST
    vld <= 1'b1;
    for (int i = 0; i < ITER_NUM; i++) begin
        addr <= $urandom();
        data <= $urandom();

        repeat(5) @(posedge clk);
    end

    // Deassert valid
    vld <= '0;
    repeat(10) @(posedge clk);
    `endif

    repeat(50) @(posedge clk);
    $finish;
end
endmodule
