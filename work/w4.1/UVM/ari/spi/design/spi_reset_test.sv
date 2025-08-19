class spi_reset_test extends spi_base_test;
  `uvm_component_utils(spi_reset_test)

  int num_iters = 1;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Read user-defined iterations from command line (+ITER=N)
    if ($value$plusargs("ITER=%d", num_iters)) begin
      `uvm_info("RESET_TEST", $sformatf("User defined iterations = %0d", num_iters), UVM_LOW)
    end
    else begin
      `uvm_info("RESET_TEST", $sformatf("Using default iterations = %0d", num_iters), UVM_LOW)
    end
  endfunction

  task run_phase(uvm_phase phase);
    seq = spi_seq::type_id::create("seq");

    phase.raise_objection(this);

    `uvm_info("RESET_TEST", "Starting reset sequence", UVM_LOW)

    repeat (num_iters) begin
      // Drive reset via agt.drv.vif
      env.agt.drv.vif.rst_n_tb <= 0;
      repeat (5) @(posedge env.agt.drv.vif.clk_tb);
      env.agt.drv.vif.rst_n_tb <= 1;

      fork
          begin
              seq.start(env.agt.sqr);
          end
          begin
              @(posedge env.agt.drv.vif.done_tb); //let test run till done
              repeat (10) @(posedge env.agt.drv.vif.clk_tb); //reset mid run

              `uvm_info("RESET_TEST", "Asserting reset mid-run", UVM_LOW)
              env.agt.drv.vif.rst_n_tb <= 0;
              repeat (10) @(posedge env.agt.drv.vif.clk_tb);
              env.agt.drv.vif.rst_n_tb <= 1;
              `uvm_info("RESET_TEST", "Deasserted reset mid-run", UVM_LOW)
          end
      join
    end
    `uvm_info("RESET_TEST", "Reset test complete", UVM_LOW)

    // Add drain time to avoid premature phase end
    phase.phase_done.set_drain_time(this, 100ns);

    phase.drop_objection(this);
  endtask
endclass