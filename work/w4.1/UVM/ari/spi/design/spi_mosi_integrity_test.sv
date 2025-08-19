class spi_mosi_integrity_test extends spi_base_test;
  `uvm_component_utils(spi_mosi_integrity_test)

  int num_iters = 1;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Read user-defined iterations from command line (+ITER=N)
    if ($value$plusargs("ITER=%d", num_iters)) begin
      `uvm_info("MOSI_INTEGRITY_TEST", $sformatf("User defined iterations = %0d", num_iters), UVM_LOW)
    end
    else begin
      `uvm_info("MOSI_INTEGRITY_TEST", $sformatf("Using default iterations = %0d", num_iters), UVM_LOW)
    end
  endfunction

  task run_phase(uvm_phase phase);
    //seq = spi_seq::type_id::create("seq");
    phase.raise_objection(this);

    `uvm_info("MOSI_INTEGRITY_TEST", "Starting TX bit-order + MOSI timing test", UVM_LOW)

    //repeat (num_iters) begin
    // Use known data pattern
    seq = spi_seq::type_id::create("seq");
    env.agt.drv.vif.tx_data_tb = 8'hA5;

    fork
      begin
        seq.start(env.agt.sqr);
      end

      begin
          bit observed_data = 1'b0;
          int idx = 7;
          bit last_mosi = 1'b0;

          @(posedge env.agt.drv.vif.sclk_tb);
          last_mosi = env.agt.drv.vif.mosi_tb;
          observed_data = env.agt.drv.vif.mosi_tb;

          // Check every SCLK cycle until all 8 bits are shifted
          while (idx >= 0) begin
            // Between sclk rising edges, MOSI must stay stable
            @(negedge env.agt.drv.vif.sclk_tb);
            if (env.agt.drv.vif.mosi_tb !== last_mosi) begin
              `uvm_error("MOSI_INTEGRITY_TEST",
                $sformatf("MOSI changed between rising edges! Prev=%0b, Now=%0b",
                          last_mosi, env.agt.drv.vif.mosi_tb))
            end

            // Check bit order
            if (observed_data !== env.agt.drv.vif.tx_data_tb[idx]) begin
              `uvm_error("MOSI_INTEGRITY_TEST",
              $sformatf("Bit order mismatch! index %0d, Expected %0b, Got %0b", idx, env.agt.drv.vif.tx_data_tb[idx], observed_data))
            end else begin
              `uvm_info("MOSI_INTEGRITY_TEST",
              $sformatf("Correct MSB-first transmission: index %0d, Expected %0b, Got %0b", idx, env.agt.drv.vif.tx_data_tb[idx], observed_data), UVM_LOW)
            end

            // At rising edge: sample MOSI bit
            @(posedge env.agt.drv.vif.sclk_tb);
            observed_data = env.agt.drv.vif.mosi_tb;
            last_mosi = env.agt.drv.vif.mosi_tb;
            idx--;
          end
        end
    join_any
    disable fork; // Once any thread finishes, disable the whole fork
    //end
    `uvm_info("MOSI_INTEGRITY_TEST", "Mosi integrity test complete", UVM_LOW)

    // Add drain time to avoid premature phase end
    phase.phase_done.set_drain_time(this, 100ns);


    phase.drop_objection(this);
  endtask
endclass