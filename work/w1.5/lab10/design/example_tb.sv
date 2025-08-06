module fsm_short_tb;
    // Inputs
    logic clock;
    logic reset;

    // Outputs
    logic r, g, y;

    // Instantiate the Unit Under Test (UUT)
    fsm_short uut (
        .r(r),
        .g(g),
        .y(y),
        .clock(clock),
        .reset(reset)
    );

    // Clock generation
    always #5 clock = ~clock;

    // Monitor to display state changes
    always @(posedge clock) begin
        $display("         Time=%0t: Reset=%0b, PS=%s, NS=%s, Timer=%0d, Lights=%b%b%b",
                 $time,
                 uut.reset,
                 uut.PS.name(),
                 uut.NS.name(),
                 uut.timer,
                 r, g, y);
    end

    // Test sequence
    initial begin
        // Initialize inputs
        clock = 0;
        reset = 0;

        // Dump waveform file
        $fsdbDumpfile("fsm_short_sim.fsdb");
        $fsdbDumpvars(0, fsm_short_tb);

        // Test 1: Reset behavior
        reset = 1;
        #10;
        reset = 0;
        #10;
	if (reset !== 0) begin
            $fatal("=Failed= Test 1: Reset asserts/de-asserts fine");
        end else begin
            $display("=Passed= Test 1: Reset asserts/de-asserts fine");
        end

        // Verify reset puts system in RED state
        if (r !== 1'b1 || g !== 1'b0 || y !== 1'b0 || uut.PS !== uut.RED) begin
            $fatal("=Failed= Test 2: Reset initializes to RED state");
        end else begin
	    $display("=Passed= Test 2: Reset initializes to RED state");
	end

        // Test 2: Full cycle test
        $display("==Info== Test 3: Full cycle test starts");

        // Wait for RED to GREEN transition (20 cycles)
	fork
            begin
                wait (uut.PS == uut.GREEN);
            end
            begin
                #300; // Timeout after 300ns
                $fatal("=Failed= Test 3: RED to GREEN transition timeouts");
            end
        join_any
        disable fork;
        if ($time != 215) begin
            $fatal("=Failed= Test 3: RED to GREEN transition (expected 215000 != got %0t)", $realtime);
        end else begin
	    $display("=Passed= Test 3: RED to GREEN transition (expected 215000 == got %0t)", $realtime);
        end

        // Wait for GREEN to YELLOW transition (15 cycles)
        wait(uut.PS == uut.YELLOW)
        $display("Transitioned to YELLOW at time %0t", $time);
        if ($time != 360) begin
            $display("Error: GREEN duration incorrect (expected 360ns, got %0tns)", $time);
            $finish;
        end

        // Wait for YELLOW to RED transition (5 cycles)
        wait(uut.PS == uut.RED);
        $display("Transitioned back to RED at time %0t", $time);
        if ($time != 410) begin
            $display("Error: YELLOW duration incorrect (expected 410ns, got %0tns)", $time);
            $finish;
        end

        // Test 3: Verify light outputs are mutually exclusive
        $display("\nTest 3: Verify light outputs");
        #100; // Let it run for a while
        if ((r & g) || (g & y) || (y & r)) begin
            $display("Error: Multiple lights active simultaneously");
            $finish;
        end

        // Test 4: Verify timer resets on state change
        $display("\nTest 4: Verify timer reset on state change");
        wait(uut.PS == uut.GREEN);
        if (uut.timer != 0) begin
            $display("Error: Timer not reset on state change (value=%0d)", uut.timer);
            $finish;
        end

        $display("\nAll tests passed successfully!");
        $finish;
    end

endmodule
