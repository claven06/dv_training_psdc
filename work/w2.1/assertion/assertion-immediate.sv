
//Immediate Assertion
//
//Assume a class called Packet is created and randomized. However this example 
//has a constraint error and randomization will fail. But, the failure will be 
//displayed as a warning message and if the user is not careful enough the test 
//may display incorrect behavior and may even appear to pass.
//an immediate assertion can be placed on the randomization method call to 
//ensure that the return value is always 1, indicating the randomization is 
//successful. If the assertion fails, it prompts the user to first look at the 
//failure thereby reducing debug efforts.
//
class Packet;
  rand bit [7:0] addr;

  constraint c_addr { addr > 5; addr < 3; }
endclass

module tb;
  initial begin
    Packet m_pkt = new();

    m_pkt.randomize();
//    assert(m_pkt.randomize());
  end
endmodule
