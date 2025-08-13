package rand_input_pkg;
  localparam SPI_TRF_BIT = 8;

  class Rand_Input;
    randc logic [1:0] req;
    rand logic [7:0] wait_duration;
    rand logic [SPI_TRF_BIT-1:0] din_master;
    rand logic [SPI_TRF_BIT-1:0] din_slave;

    constraint wait_range { wait_duration inside {[1:256]}; }
    constraint req_range { req inside {[0:3]}; }
    //constraint din_master_range { din_master inside {[8'h50:8'h51],[8'h56:8'h57],[8'hAB:8'hAC]}; }
    //constraint din_slave_range { din_slave inside {[8'h50:8'h51],[8'h56:8'h57],[8'hAB:8'hAC]}; }

    // Randomize & display
    function void randomize_and_display();
      if (!randomize()) begin
        $display("[ERROR] Randomization failed!");
      end else begin
        $display("[RANDOMIZED] req=%0b wait_duration=0x%0h din_master=0x%0h din_slave=0x%0h",
                 req, wait_duration, din_master, din_slave);
      end
    endfunction
    
  endclass
endpackage
