// Data packet in this environment
class transaction;
   rand bit [7:0] data;

   function display ();
      $display ("[%0t] Data = 0x%0h", $time, data);
   endfunction
endclass

// Generator class - Generate a transaction object and put into mailbox
class generator;
   mailbox mbx;

   function new (mailbox mbx);
      this.mbx = mbx;
   endfunction

   task genData ();
      transaction trns = new ();
      trns.randomize ();
      trns.display ();
      $display ("[%0t] [Generator] Going to put data packet into mailbox", $time);
      mbx.put (trns);
      $display ("[%0t] [Generator] Data put into mailbox", $time);
   endtask
endclass

// Driver class - Get the transaction object from Generator
class driver;
   mailbox mbx;

   function new (mailbox mbx);
      this.mbx = mbx;
   endfunction

   task drvData ();
      transaction drvTrns = new ();
      $display ("[%0t] [Driver] Waiting for available data", $time);
      mbx.get (drvTrns);
      $display ("[%0t] [Driver] Data received from Mailbox", $time);
      drvTrns.display ();
   endtask
endclass

// Top Level environment that will connect Gen and Drv with a mailbox
module tb_top;
   mailbox   mbx;
   generator Gen;
   driver    Drv;

   initial begin
      mbx = new ();
      Gen = new (mbx);
      Drv = new (mbx);

      fork
         #10 Gen.genData ();
         Drv.drvData ();
      join_none
   end
endmodule
