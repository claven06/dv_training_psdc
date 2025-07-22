module tb_mux2to1;

logic a;
logic b;
logic sel;
logic y;

mux2to1 dut (.*);

//initial begin
//    $fsdbDumpfile("dump.fsdb");
//    $fsdbDumpvars;
//    $fsdbDumpMDA;
//end

initial begin
    $vcdplusfile("dump.vpd");
    $vcdpluson;
end

initial begin
    a = '0;
    b = '0;
    sel = '0;

    #10
    a = 1'b1;

    #10
    sel = 1'b1;

    #10
    b = 1'b1;

    #10
    a = '0;
    sel = '0;

    #20
    $finish;
end

endmodule
