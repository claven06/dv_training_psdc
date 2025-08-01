module testbench;
    bit clk;    //Simulate clock signal
    bit resetn; //Simulate resetn signal
    bit d;      //Simulate data input
    bit q;      //Observe output

    int unsigned passedCnt, failedCnt;

    //Instantiate the D Flip-Flop module
    dff dff0 (
        .clk(clk),
        .resetn(resetn),
        .d(d),
        .q(q));

    //Generate clock signal
    always #5 clk = ~clk; //Clock toggles every 5 time units
    
    //test cases
    initial begin
        //Initialize signals
        resetn = 0;
        d = 0;
   
        //Simulate data changes
        #10 resetn = 1; //resetn deasserted
    
        #10 d = 1;  //Change d after 10 time units
        #20 d = 0;  //Change d after another 20 time units
        #30 d = 1;  //Change d again after 30 time units

        #10 resetn = 0; //resetn asserted
        #20 d = 1;  //change d after 20 time units
        #10 d = 0;  //change d after 10 time units

        #10 resetn = 1; //resetn deasserted
        #20 d = 1;  //change d after 20 time units
        #10 d = 0;  //change d after 10 time units
        #40 
            if(!failedCnt) $display("=== Test passed!, passedCnt = %0d ===", passedCnt);
                else $display("=== Test failed!, failedCnt = %0d ===", failedCnt);
            $finish; //End simulation after 40 time units

    end

    initial begin
        //Monitor signals
        $monitor("[Time=%0d] clk=%b resetn=%b d=%b q=%b", $time, clk, resetn, d, q);

        //Enable wave dump
        $fsdbDumpfile("fsdbdump.fsdb");
        $fsdbDumpvars;
    end

    //checker for passed or failed
    always @(posedge clk) begin
        #1
        if (!resetn)
            if (q == 0) begin
                $display ("[Time=%0d]test passed: resetn=%b q=%b d=%b", $time,resetn,q,d);
                passedCnt++;
            end
            else begin
                $display ("[Time=%0d]test failed: resetn=%b q=%b d=%b", $time,resetn,q,d);
                failedCnt++;
            end
        else begin        
            if (q == d) begin
                $display ("[Time=%0d]test passed q=%b d=%b", $time,q,d);
                passedCnt++;
            end
            else begin
                $display("[Time=%0d]test failed q=%b d=%b", $time,q,d);
                failedCnt++;
            end
        end
    end

endmodule
