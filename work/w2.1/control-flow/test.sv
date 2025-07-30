module test (
output logic [3:0] x, y, z,
input logic [1:0] a,
input logic       en
);

always_comb begin
  y = '0;
  priority case ({en,a})
    3'b100: y[a] = 1'b1;
    3'b101: y[a] = 1'b1;
    3'b110: y[a] = 1'b1;
    3'b111: y[a] = 1'b1;
  endcase
end

always_comb begin
  x = '0;
  unique case ({en,a})
    3'b100: x[a] = 1'b1;
    3'b101: x[a] = 1'b1;
    3'b110: x[a] = 1'b1;
    3'b111: x[a] = 1'b1;
  endcase
end


always_comb begin
  z = '0;
  case ({en,a})
    3'b100: z[a] = 1'b1;
    3'b101: z[a] = 1'b1;
    3'b110: z[a] = 1'b1;
    3'b111: z[a] = 1'b1;
  endcase
end
endmodule
