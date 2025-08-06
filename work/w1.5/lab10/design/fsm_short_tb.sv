module fsm_short_tb;

    logic clock;
    logic reset;
    logic r, g, y;

    assign timer = dut.timer;

    localparam RED    = 2'b00;
    localparam GREEN  = 2'b01;
    localparam YELLOW = 2'b10;

    fsm_short dut(.*);

    initial begin
        $fsdbDumpfile("waveform.fsdb");
        $fsdbDumpvars(0, fsm_short_tb);
    end

    initial begin
        clock = 0;
        forever #5 clock = ~clock;
    end

    initial begin
        reset = 1;
        repeat (2) @(posedge clock);
        reset = 0;
        repeat (2) @(posedge clock);

        repeat (1000) @(posedge clock);
        $finish;
    end

    initial begin
        $monitor("Time: %t | Red=%0d | Yellow=%0d | Green=%0d", $time, r, y, g);
    end

    // assertion check
    AST_RESET_CHECK:    assert property (@(posedge clock)
                            (reset) |-> (dut.PS == RED && timer == 0)
                        ) else $error("ERROR: PS and timer not reset.");

    AST_RED_CHECK:      assert property (@(posedge clock) disable iff (reset)
                        dut.PS == RED |-> (r == 1 && y == 0 && g == 0)
                    ) else $error("ERROR: Incorrect output in RED state.");

    AST_GREEN_CHECK:    assert property (@(posedge clock) disable iff (reset)
                        dut.PS == GREEN |-> (r == 0 && y == 0 && g == 1)
                    ) else $error("ERROR: Incorrect output in GREEN state.");

    AST_YELLOW_CHECK:   assert property (@(posedge clock) disable iff (reset)
                        dut.PS == YELLOW |-> (r == 0 && y == 1 && g == 0)
                    ) else $error("ERROR: Incorrect output in YELLOW state.");

    AST_RED_TO_GREEN:   assert property (@(posedge clock) disable iff (reset)
                        (dut.PS == RED && timer == 20) |=> (dut.NS == GREEN)
                    ) else $error("ERROR: Incorrect transtion of state.");

    AST_GREEN_TO_YELLOW:    assert property (@(posedge clock) disable iff (reset)
                            (dut.PS == GREEN && timer == 15) |=> (dut.NS == YELLOW)
                        ) else $error("ERROR: Incorrect transtion of state.");

    AST_YELLOW_TO_RED:  assert property (@(posedge clock) disable iff (reset)
                        (dut.PS == YELLOW && timer == 5) |=> (dut.NS == RED)
                    ) else $error("ERROR: Incorrect transtion of state.");



endmodule

