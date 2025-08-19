module spi_assertions #(parameter int NUM_BITS=8) (
    input logic clk,
    input logic rst_n,
    input logic start,
    input logic busy,
    input logic done,
    input logic sclk,
    input logic [2:0] bit_cnt,
    input logic [7:0] rx_data,
    input logic [7:0] tx_data,
    input logic cs_n,
    input logic mosi,
    input logic miso, 
    input logic [7:0] rx_reg,
    input logic [7:0] tx_reg
);

    logic [7:0] prev_tx_data;
    logic prev_mosi;
    logic prev_miso;
    
    // Sample tx_data on done pulse
    always @(posedge clk) begin
    if (!rst_n)
        prev_tx_data <= '0;
    else if (done)
        prev_tx_data <= tx_data;
    end

    // 2.2a. Ensure start is ignored if busy=1
    property start_ignored_when_busy;
        @(posedge clk) disable iff (!rst_n)
        (start && busy) |-> $stable(busy);
    endproperty
    AST_START_IGNORED: assert property (start_ignored_when_busy)
        else $error("Failed assertion: start was not ignored while busy");

    // 2.2b. No new transaction until done pulses
    property new_tran_after_done;
        @(posedge clk) disable iff (!rst_n)
        done |=> !done ##[1:$] start |-> (tx_data !== prev_tx_data) ;
    endproperty
    AST_NEW_TRAN_AFTER_DONE: assert property (new_tran_after_done)
        else $error("Failed assertion: No new transaction until done pulses");

    // 2.2c. Busy stays high for exactly 8 bits
    property busy_duration;
        @(posedge sclk) disable iff (!rst_n)
        ((bit_cnt == 0) && done) |-> busy;
    endproperty
    AST_BUSY_DURATION: assert property (busy_duration)
        else $error("Failed assertion: busy did not remain asserted for expected duration");

    // 2.2d. done is exactly 1 clock cycle after last bit 
    property done_one_cycle_after_busy;
        @(posedge clk) disable iff (!rst_n)
        ((bit_cnt == 0) && (rx_data != '0) && $fell(sclk)) |-> done ##1 !done;
    endproperty
    AST_DONE_1CC: assert property (done_one_cycle_after_busy)
        else $error("Failed assertion: done was not exactly 1 cycle after busy fell");

    // 2.2e. busy deasserts 1 cycle after done
    property busy_after_done;
        @(posedge clk) disable iff (!rst_n)
        done |=> !busy;
    endproperty
    AST_BUSY_AFTER_DONE: assert property (busy_after_done)
        else $error("Failed assertion: busy did not deassert 1 cycle after done");

    // 2.2f. busy goes high immediately after start
    property busy_after_start;
        @(posedge clk) disable iff (!rst_n)
        start |=> busy;
    endproperty
    AST_BUSY_AFTER_START: assert property (busy_after_start)
        else $error("Failed assertion: busy did not assert immediately after start");

    // 2.3a. cs_n low immediately after start
    property cs_n_low_after_start;
        @(posedge clk) disable iff (!rst_n)
        start |=> !cs_n;
    endproperty
    AST_CS_N_LOW_AFTER_START: assert property (cs_n_low_after_start)
        else $error("Failed assertion: cs_n low immediately after start");

    // 2.3b. cs_n has no glitch during transfer
    property cs_n_no_glitch_during_transfer;
        @(posedge clk) disable iff (!rst_n)
        start |=> (cs_n == 1'b0 throughout (!done));
    endproperty
    AST_CS_N_NO_GLITCH: assert property (cs_n_no_glitch_during_transfer)
        else $error("Failed assertion: cs_n has no glitch during transfer");

    // 2.3c. cs_n high after 8th bit (aligned with done)
    property cs_n_high_after_8th_bit;
        @(posedge clk) disable iff (!rst_n)
        ((bit_cnt == 0) && (rx_data != '0) && $fell(sclk)) |-> cs_n;
    endproperty
    AST_CS_N_HIGH_BIT8: assert property (cs_n_high_after_8th_bit)
        else $error("Failed assertion: cs_n high after 8th bit (aligned with done)");

    // 2.3d. cs_n should not deassert early (e.g: after 7 bits)
    property cs_n_no_deassert_early;
        @(posedge clk) disable iff (!rst_n)
        busy && (bit_cnt == 7) |-> (cs_n == 1'b0 throughout (!done && (bit_cnt != 0)));
    endproperty
    AST_CS_N_NO_EARLY_DEASSERT: assert property (cs_n_no_deassert_early)
        else $error("Failed assertion: cs_n should not deassert early (e.g: after 7 bits)");

    // 2.4b. Ensure mosi only changes on rising sclk edges
    property mosi_chg_on_rising_sclk;
        @(posedge clk) disable iff (!rst_n)
        busy && $changed(mosi) |-> $rose(sclk);
    endproperty
    AST_MOSI_CHG_ON_RISING_SCLK: assert property (mosi_chg_on_rising_sclk)
        else $error("Failed assertion: Ensure mosi only changes on rising sclk edges");

    // 2.5a. miso is sampled only on falling sclk edges
    property miso_sampled_on_falling_sclk;
        @(posedge clk) disable iff (!rst_n)
        busy && $changed(rx_reg[0]) |-> $fell(sclk);
        //sclk && busy |-> !sclk && (rx_reg[0] == miso);
    endproperty
    AST_MISO_SAMPLED_ON_FALLING_SCLK: assert property (miso_sampled_on_falling_sclk)
        else $error("Failed assertion: miso is sampled only on falling sclk edges");

    // 2.5c. Ensure rx_data updates only when done=1
    property rx_data_update_when_done;
        @(posedge clk) disable iff (!rst_n)
        done |-> (rx_data == rx_reg);
    endproperty
    AST_RX_DATA_UPDATE_WHEN_DONE: assert property (rx_data_update_when_done)
        else $error("Failed assertion: Ensure rx_data updates only when done=1");

    //2.6a. Aborts transaction, ensure busy=0, cs_n=1, sclk=0 start without rst_n
    property abort_trans;
        @(posedge clk)
        !rst_n |=> (busy == 1'b0) && (sclk == 1'b0) && (cs_n == 1'b1) && (start == 1'b0);
    endproperty
    AST_RABORT_TRANS: assert property (abort_trans)
        else $error("Failed assertion: Aborts transaction, ensure busy=0, cs_n=1, sclk=0 start without rst_n");    
    
    //2.6b. No operation starts until after reset
    property no_op_till_reset;
        @(posedge clk)
        rst_n |=> ##6 start |=> busy && !cs_n;
    endproperty
    AST_NO_OP_TILL_RESET: assert property (no_op_till_reset)
        else $error("Failed assertion: No operation starts until after reset");

endmodule