interface _if (
    input clk
);
    logic resetn;
    logic d;
    logic q;

    // From TB perspective
    modport TB (input q, clk, resetn, output d);
endinterface

module dff (
    input logic clk,
    input logic resetn,
    input logic d,
    output logic q
);

    always_ff @(posedge clk or negedge resetn) begin
        if (~resetn) begin
            q <= '0;
        end
        else begin
            q <= d;
        end
    end
endmodule

// module dff (
//     input clk,
//     input resetn,
//     input d,
//     output reg q
// );
//
//     always @(posedge clk) begin
//         if (!resetn) begin
//             q = '0;
//         end
//         else begin
//             q = d;
//         end
//     end
// endmodule

module tb_dff;
    logic clk;

    // Create clock
    always #10 clk = ~clk;

    // Create interface object
    _if mif (clk);

    // Instantiate DUT
    dff dut (
        .clk(clk),
        .resetn(mif.resetn),
        .d(mif.d),
        .q(mif.q)
    );

    // Assertions
    Q_ZERO_IN_RESET : assert property (@(posedge clk)
                    (~mif.resetn) |-> (mif.q == '0));

    Q_ZERO_IN_RESET_FELL : assert property (@(posedge clk)
                    $fell(mif.resetn) |-> (mif.q == '0));

    Q_1_CYCLE_AFTER_D : assert property (@(posedge clk) disable iff (~mif.resetn)
                   ((mif.d & mif.resetn) |-> ##1 mif.q));
    Q_ONLY_CHANGE_AT_POSEDGE_CLK : assert property (@(posedge clk) disable iff (~mif.resetn)
                   (mif.d
                   |-> mif.d != $past(mif.d, 1, 1, @(negedge clk))
                   |-> mif.q == $past(mif.q)));

    // Stimulus
    initial begin
        // Initialize input to 0
        clk = '0;
        mif.resetn = 1'b1;
        mif.d = '0;

        // Wait for 5 cycles, activate resetn, then wait 5 cycles, deactivate resetn
        repeat (5) @(posedge clk);
        mif.resetn <= '0;
        repeat (5) @(posedge clk);
        mif.resetn <= 1'b1;

        // Drive d for 5 iterations, with each iteration assert d for 1 cycle longer
        for (int i = 0; i < 5; i++) begin
            mif.d <= 1'b1;
            repeat (i) @(posedge clk);
            mif.d <= '0;
            repeat (20) @(posedge clk);
        end

        // Drive d at negedge clk
        repeat (5) @(negedge clk);
        mif.d <= 1'b1;
        repeat (5) @(negedge clk);
        mif.d <= '0;

        // Drive d at negedge clk for half cycle
        repeat (5) @(negedge clk);
        mif.d <= 1'b1;
        repeat (1) @(posedge clk);
        mif.d <= '0;

        // Drive d at negedge clk and change before posedge clk
        repeat (5) @(negedge clk);
        mif.d <= 1'b1;
        #8
        mif.d <= '0;

        repeat (5) @(posedge clk);
        mif.d <= 1'b1;
        repeat (5) @(negedge clk);
        mif.resetn <= '0;
        repeat (5) @(posedge clk);
        mif.resetn <= 1'b1;


        // @(negedge clk);
        // $display("%t : negedge clk (%b), mif.d (%b), $past(mif.d, 1, 1, @posedge clk) (%b), $past(mif.d, 1, 1, @negedge clk) (%b)", $time, clk, mif.d, $past(mif.d, 1, 1, @(posedge clk)), $past(mif.d, 1, 1, @(negedge clk)));
        // @(posedge clk);
        // $display("%t : posedge clk (%b), mif.d (%b), $past(mif.d, 1, 1, @posedge clk) (%b), $past(mif.d, 1, 1, @negedge clk) (%b)", $time, clk, mif.d, $past(mif.d, 1, 1, @(posedge clk)), $past(mif.d, 1, 1, @(negedge clk)));

        // Wait for 20 cycles and finish simulation
        repeat (20) @(posedge clk);
        $finish;
    end

    // Dump waveform
    initial begin
        $fsdbDumpfile("dump.fsdb");
        $fsdbDumpvars();
        $fsdbDumpMDA();
    end
endmodule
