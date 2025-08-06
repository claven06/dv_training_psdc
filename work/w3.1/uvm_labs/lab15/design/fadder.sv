module fadder(
  input logic a,      // First input bit
  input logic b,      // Second input bit
  input logic cin,    // Carry-in bit
  output logic sum,   // Sum output
  output logic cout   // Carry-out bit
);
    // Sum calculation: a XOR b XOR cin
    assign sum = a ^ b ^ cin;
    // Carry-out calculation: (a AND b) OR (cin AND (a XOR b))
    assign cout = (a & b) | (cin & (a ^ b));
endmodule
