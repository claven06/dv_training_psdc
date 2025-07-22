module tb_mux3to1;

logic a;
logic b;
logic c;
logic [1:0] sel;
logic y;

mux3to1 dut (.*);

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
    c = '0
    sel = '0;

    #10
    a = 1'b1;

    #10
    sel = 2'b01;

    #10
    b = 1'b1;

    #10
    sel = 2'b10;

    #10
    c = 1'b1;

    #10
    sel = 2'b11;

    #10
    a = '0;

    #10
    b = '0;

    #10
    c = '0;

    #20
    $finish;
end

endmodule
