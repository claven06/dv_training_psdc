module mux3to1 (
    input           logic a,
    input           logic b,
    input           logic c,
    input  [1:0]    logic sel,
    output          logic y
);

case (sel)
    3'b00: y = a;
    3'b01: y = b;
    3'b10: y = c;
    default: y = a;
endcase

endmodule
