// Sometimes we simply need to generate N random transactions to random
// locations so a generator would be useful to do just that. In this case
// loop determines how many transactions need to be sent
class generator #( int LOOP, int ADDR_WIDTH, int DATA_WIDTH );
  event drv_done, sim_done;
  mailbox drv_mbx;

  task run();
    ExtPacket #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH)) item = new();

    for (int i = 0; i < LOOP; i++) begin
      item.randomize();
      // Add immediate assertions here to skip invalid values, save simulation time
      $display ("T=%0t [Generator] Loop:%0d/%0d create next item", $time, i+1, LOOP);
      drv_mbx.put(item);
      $display ("T=%0t [Generator] Wait for driver to be done", $time);
      @(drv_done);
      $display ("T=%0t [Generator] driver done event triggered", $time);
    end
    #10 ->sim_done; //test transaction completed and send sim_done event
  endtask
endclass
