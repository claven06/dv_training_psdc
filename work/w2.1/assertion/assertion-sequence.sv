
//Assertion Sequence $rose, $fell, $stable
//
//A sequence is a simple building block in System Verilog assertions that can
//represent certain expressions to aid in creating more complex properties.
//
module tb;
    /*
  	bit a;
  	bit clk;

    ///////////////////////////////////////////////////////////////////
	// This sequence states that a should be high on every posedge clk
  	sequence s_a;
      @(posedge clk) a;
    endsequence

  	// When the above sequence is asserted, the assertion fails if 'a'
  	// is found to be not high on any posedge clk
  	assert_a:assert property(s_a);

    ///////////////////////////////////////////////////////////////////
	// This sequence states that 'a' should rise on every posedge clk
  	sequence s_rose_a;
      @(posedge clk) $rose(a);
    endsequence

  	// When the above sequence is asserted, the assertion fails if
  	// posedge 'a' is not found on every posedge clk
  	rose_a:assert property(s_rose_a);

    ///////////////////////////////////////////////////////////////////
	// This sequence states that 'a' should fall on every posedge clk
  	sequence s_fell_a;
      @(posedge clk) $fell(a);
    endsequence

  	// When the above sequence is asserted, the assertion fails if
  	// negedge 'a' is not found on every posedge clk
  	fell_a:assert property(s_fell_a);

    ///////////////////////////////////////////////////////////////////
	// This sequence states that 'a' should be stable on every clock
	// and should not have posedge/negedge at any posedge clk
  	sequence s_stable_a;
      @(posedge clk) $stable(a);
    endsequence

  	// When the above sequence is asserted, the assertion fails if
  	// 'a' toggles at any posedge clk
  	stable_a:assert property(s_stable_a);

    */
    logic clk;
    logic req;
    logic ack;
    logic rstn;

    // Assertions
    property ASSERT_ACK_AFTER_REQ_DEASSERTED;
        @(posedge clk) disable iff (!rstn) $fell(req) |-> ##1 $rose(ack);
    endproperty

    property ASSERT_REQ_1_CYCLE;
        @(posedge clk) disable iff (!rstn) req |-> ##1 (req == '0);
    endproperty

    property ASSERT_ACK_1_CYCLE;
        @(posedge clk) disable iff (!rstn) ack |-> ##1 (ack == '0);
    endproperty

    AST_ASSERT_ACK_1_CYCLE_AFTER_REQ_DEASSERTED: assert property(ASSERT_ACK_1_CYCLE_AFTER_REQ_DEASSERTED);
    AST_ASSERT_REQ_1_CYCLE: assert property(ASSERT_REQ_1_CYCLE);
    AST_ASSERT_ACK_1_CYCLE: assert property(ASSERT_ACK_1_CYCLE);

    // RTL
    logic last_req;
    logic edge_detect;

    assign edge_detect = req ^ last_req;

    always_ff @(posedge clk or negedge rstn) begin
        if(~rstn) begin
            last_req <= '0;
            ack <= '0;
        end
        else begin
            last_req <= req;
            ack <= last_req & edge_detect;
        end
    end

    ///////////////////////////////////////////////////////////////////

    // 20ns clk
	always #10 clk = ~clk;

    /*
	initial begin
      for (int i = 0; i < 10; i++) begin
        a = $random;
        @(posedge clk);

        // Assertion is evaluated in the preponed region and
        // use $display to see the value of 'a' in that region
        $display("[%0t] a=%0d", $time, a);
      end
      #20 $finish;
    end
    */

    // Testbench stimulus
    initial begin
        $monitor("%t : req = %b, ack = %b\n", $time, req, ack);
        clk = '0;
        req = '0;
        rstn = '0;


        repeat (5) @(posedge clk);
        rstn <= 1'b1;
        req <= 1'b1;

        repeat (1) @(posedge clk);
        req <= '0;

        repeat (5) @(posedge clk);
        req <= 1'b1;

        repeat (2) @(posedge clk);
        req <= 1'b0;

        repeat (5) @(posedge clk);
        force ack = 1'b1;

        repeat (2) @(posedge clk);
        release ack;

        repeat (10) @(posedge clk);
        $finish;
    end

    initial begin
        $fsdbDumpfile("dump.fsdb");
        $fsdbDumpvars(0, tb);
    end
endmodule
