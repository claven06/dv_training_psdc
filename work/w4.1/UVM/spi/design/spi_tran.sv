// To verify that the adder adds, we also need to check that it
// does not add when rstn is 0, and hence rstn should also be
// randomized along with a and b.
class Packet #( int ADDR_WIDTH, int DATA_WIDTH );
  rand  bit                     rstn;
  rand  bit                     vld;
  randc bit [ADDR_WIDTH-1:0]    addr;
  randc bit [DATA_WIDTH-1:0]    data;
  bit [ADDR_WIDTH-1:0]    addr_a;
  bit [DATA_WIDTH-1:0]    data_a;
  bit [ADDR_WIDTH-1:0]    addr_b;
  bit [DATA_WIDTH-1:0]    data_b;

  function void print(string tag="");
    $display ("T=%0t %s rstn=0x%0h vld=0x%0h addr=0x%0h data=0x%0h addr_a=0x%0h data_a=0x%0h addr_b=0x%0h data_b=0x%0h",
  $time, tag, rstn, vld, addr, data, addr_a, data_a, addr_b, data_b);
  endfunction

  // This is a utility function to allow copying contents in
  // one Packet variable to another.
  function void copy(Packet #(.DATA_WIDTH(DATA_WIDTH), .ADDR_WIDTH(ADDR_WIDTH)) tmp);
    this.rstn = tmp.rstn;
    this.vld = tmp.vld;
    this.addr = tmp.addr;
    this.data = tmp.data;
    this.addr_a = tmp.addr_a;
    this.data_a = tmp.data_a;
    this.addr_b = tmp.addr_b;
    this.data_b = tmp.data_b;
  endfunction
endclass

class ExtPacket #( int ADDR_WIDTH, int DATA_WIDTH ) extends Packet #( .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH) );
    constraint minimize_rstn_assertion { rstn dist {0:=20, 1:=80};}
    constraint minimize_vld_assertion { vld dist {0:=20, 1:=80};}
endclass
