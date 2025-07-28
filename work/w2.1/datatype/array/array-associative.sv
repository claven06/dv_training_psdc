module tb;
    int imem[int];

    initial begin
        imem[3] =1;
        imem[16'hffff] = 2;
        imem[32'h12345678] = 32'd7890_1234;
        imem[4'b1000] = 3;

        // prints "3 entries, 3 sizes" 
        $display("===============================");
        $display("imem size is %0d with %0d entries", imem.size, imem.num);
        $display("imem = %p", imem);
        $display("===============================");
    end

endmodule
