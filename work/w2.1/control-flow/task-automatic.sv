module tb;
  initial display();
  initial display();
  initial display();
  initial display();

  // This is an automatic task
  task automatic display();
    integer i = 0;
    i = i + 1;
    $display("i=%0d", i);
  endtask

endmodule
