module tb;
  initial begin
  	// 1. Declare an integer variable to hold the file descriptor
  	int fd;

  	// 2. Open a file called "note.txt" in the current folder with a "read" permission
  	// If the file does not exist, then fd will be zero
    fd = $fopen ("./note.txt", "r");
    if (fd)  $display("File was opened successfully : %0d", fd);
    else     $display("File was NOT opened successfully : %0d", fd);

    // 2. Open a file called "note.txt" in the current folder with a "write" permission
    //    "fd" now points to the same file, but in write mode
    fd = $fopen ("./note.txt", "w");
    if (fd)  $display("File was opened successfully : %0d", fd);
    else     $display("File was NOT opened successfully : %0d", fd);

    // 3. Close the file descriptor
    $fclose(fd);
  end
endmodule
