class spi_base_test extends uvm_test;
  `uvm_component_utils(spi_base_test)

  spi_env env;
  spi_seq seq;
  int num_iters = 1; // default number of iterations

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = spi_env::type_id::create("env", this);

    // Read user-defined iterations from command line (+ITER=N)
    if ($value$plusargs("ITER=%d", num_iters)) begin
      `uvm_info("BASE_TEST", $sformatf("User defined iterations = %0d", num_iters), UVM_LOW)
    end
    else begin
      `uvm_info("BASE_TEST", $sformatf("Using default iterations = %0d", num_iters), UVM_LOW)
    end
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    `uvm_info("BASE_TEST", "Base test running", UVM_LOW)

    // Run the sequence repeatedly
    repeat (num_iters) begin
      seq = spi_seq::type_id::create($sformatf("seq_%0d", num_iters));
      seq.start(env.agt.sqr);
    end

    phase.drop_objection(this);
  endtask
endclass