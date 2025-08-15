module spi_slave
    #(parameter SPI_MODE = 1,
      parameter SPI_TRF_BIT = 12)
(
	input clk,
	input sclk,
	input rst,
	input[(SPI_TRF_BIT-1):0] din,
	input cs,
	input mosi,
	output miso,
	output[(SPI_TRF_BIT-1):0] dout
);

    // states of the receiver
    typedef enum {
        IDLE_RX,
        GET_DATA
    } state_rx_t;

    typedef enum {
        IDLE_TX,
        SEND_DATA
    } state_tx_t;

    state_rx_t state_rx, next_state_rx;
    state_tx_t state_tx, next_state_tx;

    // temporary registers
    logic miso_temp, next_miso_temp;
    logic [(SPI_TRF_BIT-1):0] din_temp, next_din_temp;
    logic [(SPI_TRF_BIT-1):0] dout_temp, next_dout_temp;

    // data bit counters
    logic [3:0] data_index_tx, next_data_index_tx;
    logic [3:0] data_index_rx, next_data_index_rx;

 // edge detection for tx & rx
    logic sclk_previous_value;
    logic sclk_posedge, sclk_negedge;

    always_ff @(posedge clk) begin
        sclk_previous_value <= sclk;
    end

	assign sclk_posedge = (~sclk_previous_value) & sclk; // positive edge detection (for transmitter)
	assign sclk_negedge = sclk_previous_value & (~sclk); // negative edge detection (for receiver)


    // FSM state change
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            state_tx <= IDLE_TX;
            din_temp <= '0;
            data_index_tx <= '0;
            miso_temp <= '0;

            state_rx <= IDLE_RX;
            data_index_rx <= '0;
            dout_temp <= '0;
        end
        else begin
            state_tx <= next_state_tx;
            din_temp <= next_din_temp;
            data_index_tx <= next_data_index_tx;
            miso_temp <= next_miso_temp;

            state_rx <= next_state_rx;
            data_index_rx <= next_data_index_rx;
            dout_temp <= next_dout_temp;
        end
    end

    // FSM operation
    always_comb begin
        // Hold current values
        next_state_tx          = state_tx;
        next_din_temp          = din_temp;
        next_data_index_tx     = data_index_tx;
        next_miso_temp         = miso_temp;

        case(state_tx)
            IDLE_TX: begin
                next_din_temp = '0;
                next_data_index_tx = '0;
                next_miso_temp = '0;
                if (!cs) begin
                    next_din_temp = din;
                    next_state_tx = SEND_DATA;
                end
            end
            SEND_DATA: begin
                if (sclk_posedge) begin
                    if (data_index_tx <= (SPI_TRF_BIT-1)) begin
                        next_miso_temp = din_temp[(SPI_TRF_BIT-1) - data_index_tx]; // MSB is sent first
                        next_data_index_tx = data_index_tx + 1;
                    end
                    else begin
                        next_din_temp = '0;
                        next_data_index_tx = '0;
                        next_miso_temp = '0;
                        next_state_tx = IDLE_TX;
                    end
                end
                else if (cs) begin
                    next_din_temp = '0;
                    next_data_index_tx = '0;
                    next_miso_temp = '0;
                    next_state_tx = IDLE_TX;
                end
            end
            default : next_state_tx = IDLE_TX;
        endcase
    end

    always_comb begin
        // Hold current values
        next_state_rx       = state_rx;
        next_data_index_rx  = data_index_rx;
        next_dout_temp      = dout_temp;

        case(state_rx)
            IDLE_RX: begin
                next_data_index_rx = '0;
                if (!cs) begin
                    next_state_rx = GET_DATA;
                end
            end
            GET_DATA: begin
                if (sclk_negedge) begin
                    if (data_index_rx <= (SPI_TRF_BIT-1)) begin
                        next_data_index_rx = data_index_rx + 1;
                        next_dout_temp = {dout_temp[(SPI_TRF_BIT-2):0], mosi};
                        if (data_index_rx == (SPI_TRF_BIT-1)) begin
                            next_data_index_rx = '0;
                            next_state_rx = IDLE_RX;
                        end
                    end
                    else begin
                        next_data_index_rx = '0;
                        next_dout_temp = '0;
                        next_state_rx = IDLE_RX;
                    end
                end
                else if (cs) begin
                    next_data_index_rx = '0;
                    next_dout_temp = '0;
                    next_state_rx = IDLE_RX;
                end

            end
            default : next_state_rx = IDLE_RX;
        endcase
    end

	assign miso = miso_temp;
	assign dout = dout_temp;
endmodule