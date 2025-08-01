// To verify that the adder adds, we also need to check that it
// does not add when rstn is 0, and hence rstn should also be
// randomized along with a and b.
class Packet;
  randc bit         rstn;
  randc bit[7:0]    a;
  randc bit[7:0]    b;
  bit [7:0] 	    sum;
  bit 			    carry;

  // Print contents of the data packet
  function void print(string tag="");
    $display ("T=%0t %s rstn=0x%0h a=0x%0h b=0x%0h sum=0x%0h carry=0x%0h",
        $time, tag, rstn, a, b, sum, carry);
  endfunction

  // This is a utility function to allow copying contents in
  // one Packet variable to another.
  function void copy(Packet tmp);
    this.a = tmp.a;
    this.b = tmp.b;
    this.rstn = tmp.rstn;
    this.sum = tmp.sum;
    this.carry = tmp.carry;
  endfunction
endclass

class ExtPacket extends Packet;
/*
    constraint c_input_valid_range {
        a inside {[3:7]};
        b inside {['h1a:'h1f]};
    }
    constraint c_reset_deasserted {
        rstn == 1;
    }
*/
endclass
