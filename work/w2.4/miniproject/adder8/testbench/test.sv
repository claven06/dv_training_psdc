// The test can instantiate any environment.
class test;
  env e0;

  function new();
    e0 = new();
  endfunction

  virtual task run();
    e0.run();
  endtask
endclass
