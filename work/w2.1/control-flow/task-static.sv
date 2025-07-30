module tb;
  initial display();
  initial display();
  initial display();
  initial display();

  // This is a static task
  task display();
    integer i = 0;
    i = i + 1;
    $display("i=%0d", i);
  endtask

endmodule
