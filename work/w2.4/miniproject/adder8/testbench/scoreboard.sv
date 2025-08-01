// The scoreboard is responsible to check data integrity. Since the design
// simple adds inputs to give sum and carry, scoreboard helps to check if the
// output has changed for given set of inputs based on expected logic
class scoreboard;
  mailbox scb_mbx;

  task run();
    forever begin
      Packet item, ref_item;

      $display("T=%0t [Scoreboard] run task and waiting for item", $time);

      scb_mbx.get(item);
      item.print("Scoreboard");

      // Copy contents from received packet into a new packet so
      // just to get a and b.
      ref_item = new();
      ref_item.copy(item);

      // Let us calculate the expected values in carry and sum
      if (ref_item.rstn)
      	{ref_item.carry, ref_item.sum} = ref_item.a + ref_item.b;
      else
      {ref_item.carry, ref_item.sum} = 0;

      // Now, carry and sum outputs in the reference variable can be compared
      // with those in the received packet
      if (ref_item.carry != item.carry) begin
        $display("T=%0t Scoreboard Error! Carry mismatch ref_item=0x%0h item=0x%0h",
            $time, ref_item.carry, item.carry);
      end else begin
        $display("T=%0t Scoreboard Pass! Carry match ref_item=0x%0h item=0x%0h",
            $time, ref_item.carry, item.carry);
      end

      if (ref_item.sum != item.sum) begin
        $display("T=%0t Scoreboard Error! Sum mismatch ref_item=0x%0h item=0x%0h",
             $time, ref_item.sum, item.sum);
      end else begin
        $display("T=%0t Scoreboard Pass! Sum match ref_item=0x%0h item=0x%0h",
            $time, ref_item.sum, item.sum);
      end
    end
  endtask
endclass
