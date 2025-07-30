module tb;
  int 	 fd; 			// Variable for file descriptor handle
  int 	 idx;
  string str;

  initial begin
    // 1. Lets first open a new file and write some contents into it
    fd = $fopen ("trial", "w");
    for (int i = 0; i < 5; i++)
      $fdisplay (fd, "Iteration = %0d", i);
    $fclose(fd);


    // 2. Let us now read back the data we wrote in the previous step
    fd = $fopen ("trial", "r");

    // fscanf returns the number of matches
    while ($fscanf (fd, "%s = %0d", str, idx) == 2) begin
      $display ("Line: %s = %0d", str, idx);
    end

    // Close this file handle
    $fclose(fd);
  end
endmodule
