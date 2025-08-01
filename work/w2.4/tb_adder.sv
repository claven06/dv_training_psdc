module adder #(
    parameter int DATA_WIDTH = 8
) (
    input  logic                    clk,
    input  logic                    rstn,
    input  logic [DATA_WIDTH-1:0]   a,
    input  logic [DATA_WIDTH-1:0]   b,
    output logic [DATA_WIDTH-1:0]   sum,
    output logic                    carry
);
    logic [DATA_WIDTH-1:0]  result_sum;
    logic                   result_carry;

    assign {result_carry, result_sum} = a + b;

    always_ff @(posedge clk or negedge rstn) begin
        if (~rstn) begin
            sum <= '0;
            carry <= '0;
        end
        else begin
            sum <= result_sum;
            carry <= result_carry;
        end
    end
endmodule

interface adder_if #(
    parameter int DATA_WIDTH = 8
) (
    input clk
);
    logic                    rstn;
    logic [DATA_WIDTH-1:0]   a;
    logic [DATA_WIDTH-1:0]   b;
    logic [DATA_WIDTH-1:0]   sum;
    logic                    carry;
endinterface

class adder_packet #(
    parameter int DATA_WIDTH = 8
);
    rand bit                    rstn;
    rand bit [DATA_WIDTH-1:0]   a;
    rand bit [DATA_WIDTH-1:0]   b;

    constraint c_input_valid_range {
        a inside {[3:7]};
        b inside {['h1a:'h1f]};
    }
    constraint c_reset_deasserted {
        rstn == 1;
    }

    function void apply_to_signals (
        ref logic                  rstn_out,
        ref logic [DATA_WIDTH-1:0] a_out, b_out
    );
        rstn_out = rstn;
        a_out = a;
        b_out = b;
    endfunction
endclass

module tb_adder;
    logic clk;

    always #10 clk = ~clk;

    adder_if mif (clk);
    adder_packet mpkt;

    adder dut (
        .clk(clk),
        .rstn(mif.rstn),
        .a(mif.a),
        .b(mif.b),
        .sum(mif.sum),
        .carry(mif.carry)
    );

    initial begin
        clk = '0;
        $monitor("Time %t: rstn (%0b), a (%0d), b (%0d), sum (%0d), carry (%0b)", $time, mif.rstn, mif.a, mif.b, mif.sum, mif.carry);
        mpkt = new ();

        repeat (5) @(posedge clk);

        for (int i = 0; i < 5; i++) begin
            assert (mpkt.randomize ());
            $display("Time %t: Randomized: rstn = %0b, a = %0d, b = %0d", $time, mpkt.rstn, mpkt.a, mpkt.b);
            mpkt.apply_to_signals (mif.rstn, mif.a, mif.b);
        end

        repeat (20) @(posedge clk);
        $finish;
    end


    initial begin
        $fsdbDumpfile("dump.fsdb");
        $fsdbDumpvars();
        $fsdbDumpMDA();
    end
endmodule
