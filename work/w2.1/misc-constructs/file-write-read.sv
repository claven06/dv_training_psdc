module tb;
  int 	 fd; 			// Variable for file descriptor handle
  string line; 			// String value read from the file

  initial begin
    // 1. Lets first open a new file and write some contents into it
    fd = $fopen ("trial", "w");
    for (int i = 0; i < 5; i++) begin
      $fdisplay (fd, "Iteration = %0d", i);
    end
    $fclose(fd);


    // 2. Let us now read back the data we wrote in the previous step
    fd = $fopen ("trial", "r");

    while (!$feof(fd)) begin
      $fgets(line, fd);
      $display ("Line: %s", line);
    end

    // Close this file handle
    $fclose(fd);
  end
endmodule
