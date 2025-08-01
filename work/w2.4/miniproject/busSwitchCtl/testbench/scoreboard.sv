// The scoreboard is responsible to check data integrity. Since the design
// simple adds inputs to give sum and carry, scoreboard helps to check if the
// output has changed for given set of inputs based on expected logic
class scoreboard #( int ADDR_WIDTH, int DATA_WIDTH, bit [ADDR_WIDTH-1:0] ADDR_DIV );
  int flop_stage = 1;
  int count = 0;
  mailbox scb_mbx_in;
  mailbox scb_mbx_out;
  Packet #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH)) queue_in[$];
  Packet #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH)) item_from_in, ref_item_calc;
  Packet #(.ADDR_WIDTH(ADDR_WIDTH), .DATA_WIDTH(DATA_WIDTH)) item_from_out, ref_item_from_in;

  task run();
      ref_item_calc = new();
      ref_item_from_in = new();
    fork
      forever begin
        $display("T=%0t [Scoreboard] run task and waiting for item_from_in", $time);
        scb_mbx_in.get(item_from_in);

        item_from_in.print("Scoreboard item_from_in: ");

        if (item_from_in.rstn) begin
          if (item_from_in.vld) begin
            if (item_from_in.addr <= ADDR_DIV) begin
              ref_item_calc.addr_a <= item_from_in.addr;
              ref_item_calc.data_a <= item_from_in.data;
              ref_item_calc.addr_b <= 0;
              ref_item_calc.data_b <= 0;
            end
            else begin
              ref_item_calc.addr_a <= 0;
              ref_item_calc.data_a <= 0;
              ref_item_calc.addr_b <= item_from_in.addr;
              ref_item_calc.data_b <= item_from_in.data;
            end
          end
        end
        else begin
          ref_item_calc.addr_a <= 0;
          ref_item_calc.data_a <= 0;
          ref_item_calc.addr_b <= 0;
          ref_item_calc.data_b <= 0;
        end

        queue_in.push_back(ref_item_calc);
      end
      forever begin
        $display("T=%0t [Scoreboard] run task and waiting for item_from_out", $time);
        scb_mbx_out.get(item_from_out);
        item_from_out.print("Scoreboard item_from_out: ");
        if (count < flop_stage) begin
            count++;
            continue;
        end

        if (queue_in.size() == 0) begin
          $display("T=%0t [Scoreboard] Error - Queue is empty!", $time);
        end
        else begin
          ref_item_from_in = queue_in.pop_front();
          ref_item_from_in.print("Scoreboard ref_item_from_in: ");


          if (ref_item_from_in.addr_a != item_from_out.addr_a) begin
            $display("T=%0t Scoreboard Error! addr_a mismatch ref_item_from_in=0x%0h item_from_out=0x%0h",
                $time, ref_item_from_in.addr_a, item_from_out.addr_a);
          end else begin
            $display("T=%0t Scoreboard Pass! addr_a match ref_item_from_in=0x%0h item_from_out=0x%0h",
                $time, ref_item_from_in.addr_a, item_from_out.addr_a);
          end

          if (ref_item_from_in.data_a != item_from_out.data_a) begin
            $display("T=%0t Scoreboard Error! data_a mismatch ref_item_from_in=0x%0h item_from_out=0x%0h",
                 $time, ref_item_from_in.data_a, item_from_out.data_a);
          end else begin
            $display("T=%0t Scoreboard Pass! data_a match ref_item_from_in=0x%0h item_from_out=0x%0h",
                $time, ref_item_from_in.data_a, item_from_out.data_a);
          end

          if (ref_item_from_in.addr_b != item_from_out.addr_b) begin
            $display("T=%0t Scoreboard Error! addr_b mismatch ref_item_from_in=0x%0h item_from_out=0x%0h",
                $time, ref_item_from_in.addr_b, item_from_out.addr_b);
          end else begin
            $display("T=%0t Scoreboard Pass! addr_b match ref_item_from_in=0x%0h item_from_out=0x%0h",
                $time, ref_item_from_in.addr_b, item_from_out.addr_b);
          end

          if (ref_item_from_in.data_b != item_from_out.data_b) begin
            $display("T=%0t Scoreboard Error! data_b mismatch ref_item_from_in=0x%0h item_from_out=0x%0h",
                 $time, ref_item_from_in.data_b, item_from_out.data_b);
          end else begin
            $display("T=%0t Scoreboard Pass! data_b match ref_item_from_in=0x%0h item_from_out=0x%0h",
                 $time, ref_item_from_in.data_b, item_from_out.data_b);
          end
        end
      end
    join_any
  endtask
endclass
