module tb_fa;

logic a, b, cin, s, cout;

fa dut (.*);

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
    cin = '0;

    for (int i = 0; i < 8; i++) begin
        #10 {a, b, cin} = i;
    end

    #20 $finish;
end


endmodule
