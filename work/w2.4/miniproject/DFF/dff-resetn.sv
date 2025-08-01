module dff (clk,resetn,d,q);
    input clk;      // Clock input
    input resetn;   // resetn input
    input d;        // data input
    output reg q;   // Output (stored data)

    always @(posedge clk or negedge resetn) begin
        if (!resetn)
            q = 0;     
        else
            q = d; // Assign input d to output q on clock's rising edge
    end
endmodule
