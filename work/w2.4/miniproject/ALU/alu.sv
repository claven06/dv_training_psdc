module simple_alu (
  input logic        clk,
  input logic [7:0]  a,
  input logic [7:0]  b,
  input logic [2:0]  opcode,
  output logic [15:0] result
);

  // Opcodes
  localparam ADD  = 3'b000;
  localparam SUB  = 3'b001;
  localparam AND  = 3'b010;
  localparam OR   = 3'b011;
  localparam XOR  = 3'b100;
  localparam MUL  = 3'b101;
  localparam XNOR = 3'b110;

  always_ff @(posedge clk) begin
    case (opcode)
      ADD:   result <= a + b;
      SUB:   result <= a - b;
      AND:   result <= {8'b0, a & b};
      OR:    result <= {8'b0, a | b};
      XOR:   result <= {8'b0, a ^ b};
      MUL:   result <= a * b;
      XNOR:  result <= {8'b0, ~(a ^ b)};
      default: result <= 16'hDEAD; // fallback value
    endcase
  end

endmodule
