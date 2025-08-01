module tb_alu;

  // DUT inputs
  logic clk;
  logic [7:0] a, b;
  logic [2:0] opcode;

  // DUT output
  logic [15:0] result;

  // Instantiate the ALU
  simple_alu dut (
    .clk(clk),
    .a(a),
    .b(b),
    .opcode(opcode),
    .result(result)
  );

  // Clock generation
  initial clk = 0;
  always #5 clk = ~clk;

  // Test procedure
  initial begin
    $display("Time\tOpcode\tA\tB\tResult");
    $monitor("%03t\t%04b\t%03d\t%03d\t%05d(0x%04h)", $time, opcode, a, b, result, result);

    // Apply test vectors
    a = 8'd10; b = 8'd5;
    opcode = 3'b000;

    @(posedge clk);
    opcode = 3'b000; @(posedge clk); // ADD
    opcode = 3'b001; @(posedge clk); // SUB
    opcode = 3'b010; @(posedge clk); // AND
    opcode = 3'b011; @(posedge clk); // OR
    opcode = 3'b100; @(posedge clk); // XOR
    opcode = 3'b101; @(posedge clk); // MUL
    opcode = 3'b110; @(posedge clk); // XNOR

    // Try edge cases
    a = 8'hFF; b = 8'h01;
    opcode = 3'b000; @(posedge clk); // ADD overflow

    a = 8'd0; b = 8'd0;
    opcode = 3'b001; @(posedge clk); // SUB zero

    a = 8'd0; b = 8'd1;
    opcode = 3'b001; @(posedge clk); // SUB underflow

    $display("Testbench complete.");
    $finish;
  end

endmodule
