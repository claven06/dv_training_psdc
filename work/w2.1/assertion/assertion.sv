
// Example sequence assert
// 
// The first sequence s_ab validates that b is high the next clock when 
// a is high, and the second sequence s_cd validates that d is high 2 clocks 
// after c is found high. The property asserts that the second sequence,s_cd, 
// is on the next cycle after the first sequence, s_ab.
//
module tb;
  bit a, b, c, d;
  bit clk;

  always #10 clk = ~clk;

  int i;
  initial begin
    for (i = 0; i < 20; i++) begin
      {a, b, c, d} = $random;
      $display("[T=%0t][i=%0d] a=%0d b=%0d c=%0d d=%0d", $time, i, a, b, c, d);
      @(posedge clk);
    end
    #10 
    $display("[T=%0t][i=%0d] a=%0d b=%0d c=%0d d=%0d", $time, i, a, b, c, d);
    $finish;
  end

  sequence s_ab;
    a ##1 b;
  endsequence

  sequence s_cd;
    c ##2 d;
  endsequence

  property p_expr;
    @(posedge clk) s_ab ##1 s_cd;
  endproperty

  assert property (p_expr);
endmodule
