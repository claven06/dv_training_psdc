class spi_reset_test extends spi_base_test;
  `uvm_component_utils(spi_reset_test)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  task run_phase(uvm_phase phase);
    seq = spi_seq::type_id::create("seq");

    phase.raise_objection(this);

    `uvm_info("RESET_TEST", "Starting reset sequence", UVM_LOW)

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

    `uvm_info("RESET_TEST", "Reset test complete", UVM_LOW)

    // Add drain time to avoid premature phase end
    phase.phase_done.set_drain_time(this, 100ns);

    phase.drop_objection(this);
  endtask
endclass