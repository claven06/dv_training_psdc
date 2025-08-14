// The test can instantiate any environment.
class test #( int LOOP, int ADDR_WIDTH, int DATA_WIDTH, bit [ADDR_WIDTH-1:0] ADDR_DIV );
  env #(.LOOP(LOOP), .ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH), .ADDR_DIV(ADDR_DIV)) e0;

  function new();
    e0 = new();
  endfunction

  virtual task run();
    e0.run();
  endtask
endclass
