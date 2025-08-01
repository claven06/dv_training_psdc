// An adder is combinational logic and does not
// have a clock

module my_adder8 (adder_if _if);
  always_comb begin
    if (!_if.rstn) begin
      _if.sum <= 0;
      _if.carry <= 0;
    end else begin
      {_if.carry, _if.sum} <= _if.a + _if.b;
    end
  end
endmodule
