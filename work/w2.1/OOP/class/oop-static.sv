class Packet;
  static int pkt_count = 0;
//  int pkt_count = 0;

  function new();
    pkt_count++;
  endfunction

  static function void show_count();
//  function void show_count();
    $display("Total packets created = %0d", pkt_count);
  endfunction
endclass

module tb;
  initial begin
    Packet p1 = new();
    Packet p2 = new();
    Packet::show_count(); // Legal: called without object

    p2.show_count();      // Also legal, but not recommended
    p1.show_count();      //

  end
endmodule

// Exercise:
// 1. remove line 2 static and compile, what do you find out and why?
// 2. remove all the static and compile, what do you find out and why?
// 3. resolve the compile issue for item 2 and recompile, what do you find out
// and why?
//
