class spi_clock_test extends spi_base_test;
  `uvm_component_utils(spi_clock_test)

  int num_iters = 1;

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Read user-defined iterations from command line (+ITER=N)
    if ($value$plusargs("ITER=%d", num_iters)) begin
      `uvm_info("CLOCK_TEST", $sformatf("User defined iterations = %0d", num_iters), UVM_LOW)
    end
    else begin
      `uvm_info("CLOCK_TEST", $sformatf("Using default iterations = %0d", num_iters), UVM_LOW)
    end
  endfunction

  task run_phase(uvm_phase phase); 
    time t1, t2, measured_period;
    time clk_period;
    int  clk_div;

    seq = spi_seq::type_id::create("seq");

    phase.raise_objection(this);
    `uvm_info("CLOCK_TEST", "Starting clock test", UVM_LOW)

    clk_div = env.agt.drv.vif.CLK_DIV; 

    repeat (num_iters) begin
      fork
          begin
              seq.start(env.agt.sqr);
          end
          begin
              forever begin
                  // Measure reference clk period
                  @(posedge env.agt.drv.vif.clk_tb); t1 = $time;
                  @(posedge env.agt.drv.vif.clk_tb); t2 = $time;
                  clk_period = t2 - t1;
                  `uvm_info("CLOCK_TEST", $sformatf("Measured clk_period=%0t", clk_period), UVM_LOW)

                  // ==== 2a. Verify SCLK period ====
                  @(posedge env.agt.drv.vif.sclk_tb); t1 = $time;
                  @(posedge env.agt.drv.vif.sclk_tb); t2 = $time;
                  measured_period = t2 - t1;

                  if (measured_period == 2*clk_div*clk_period)
                  `uvm_info("CLOCK_TEST", $sformatf("SCLK period OK = %0t", measured_period), UVM_LOW)
                  else
                  `uvm_error("CLOCK_TEST", $sformatf("SCLK period mismatch! Measured=%0t Expected=%0t",
                                                      measured_period, 2*clk_div*clk_period))
              end
          end
          // ==== 2b. Confirm SCLK idle ====
          begin
              forever begin
              @(posedge env.agt.drv.vif.clk_tb);
              if (env.agt.drv.vif.cs_n_tb == 1 && env.agt.drv.vif.sclk_tb !== 0)
                  `uvm_error("CLOCK_TEST", "SCLK not 0 while CS_N=1 (idle state)")
              end
          end
      join_any
      disable fork; // Once any thread finishes, disable the whole fork
    end

    `uvm_info("CLOCK_TEST", "Clock test complete", UVM_LOW)

    // Add drain time to avoid premature phase end
    phase.phase_done.set_drain_time(this, 100ns);

    phase.drop_objection(this);
  endtask
endclass
