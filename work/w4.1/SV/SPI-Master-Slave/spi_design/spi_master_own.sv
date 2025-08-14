module spi_master
    #(parameter SPI_MODE = 1,
      parameter SPI_TRF_BIT = 12)
(
	input clk,
	input sclk,
	input rst,
	input[1:0] req,
	input[(SPI_TRF_BIT-1):0] din,
	input[7:0] wait_duration,
	input miso,
	output[(SPI_TRF_BIT-1):0] dout,
	output sclk_en,
	output cs,
	output mosi,
	output done_tx,
	output done_rx
);

    // states of the receiver
    typedef enum {
        IDLE_RX,
        GET_DATA
    } state_rx_t;

    typedef enum {
        IDLE_TX,
        WAIT_STATE_1,
        SEND_DATA,
        WAIT_STATE_2
    } state_tx_t;

    state_rx_t state_rx, next_state_rx;
    state_tx_t state_tx, next_state_tx;

    // wait registers
    logic [7:0] wait_counter, next_wait_counter;
    logic [7:0] wait_duration_reg, next_wait_duration_reg;

    // temporary registers
    logic mosi_temp, next_mosi_temp;
    logic done_temp_rx, next_done_temp_rx;
    logic done_temp_tx, next_done_temp_tx;
    logic [(SPI_TRF_BIT-1):0] din_temp, next_din_temp;
    logic [(SPI_TRF_BIT-1):0] dout_temp, next_dout_temp;

    // data bit counters
    logic [3:0] data_index_tx, next_data_index_tx;
    logic [3:0] data_index_rx, next_data_index_rx;

    // request handling
    logic [1:0] req_temp;

    // handshake for tx & rx
    logic tx_start;

    // edge detection for tx & rx
    logic sclk_previous_value;
    logic sclk_posedge, sclk_negedge;

    always_ff @(posedge clk) begin
        sclk_previous_value <= sclk;
    end

	assign sclk_posedge = (~sclk_previous_value) & sclk; // positive edge detection (for transmitter)
	assign sclk_negedge = sclk_previous_value & (~sclk); // negative edge detection (for receiver)

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            req_temp <= '0;
        end
        else begin
            if (next_state_tx == IDLE_TX && next_state_rx == IDLE_RX) begin
                req_temp <= req;
            end
            else begin
                if (next_state_tx == SEND_DATA && next_state_rx == GET_DATA) begin
                    req_temp <= 2'b00;
                end
            end
        end
    end

    // FSM state change
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            state_tx <= IDLE_TX;
            din_temp <= '0;
            data_index_tx <= '0;
            done_temp_tx <= '0;
            mosi_temp <= '0;
            wait_counter <= '0;
            wait_duration_reg <= '0;

            state_rx <= IDLE_RX;
            done_temp_rx <= '0;
            data_index_rx <= '0;
            dout_temp <= '0;
        end
        else begin
            state_tx <= next_state_tx;
            din_temp <= next_din_temp;
            data_index_tx <= next_data_index_tx;
            done_temp_tx <= next_done_temp_tx;
            mosi_temp <= next_mosi_temp;
            wait_counter <= next_wait_counter;
            wait_duration_reg <= next_wait_duration_reg;

            state_rx <= next_state_rx;
            done_temp_rx <= next_done_temp_rx;
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
        next_mosi_temp         = mosi_temp;
        next_done_temp_tx      = done_temp_tx;
        next_wait_counter      = wait_counter;
        next_wait_duration_reg = wait_duration_reg;

        // Handshake
        tx_start = '0;

        case(state_tx)
            IDLE_TX: begin
                next_din_temp = '0;
                next_data_index_tx = '0;
                next_mosi_temp = '0;
                next_done_temp_tx = '0;
                next_wait_counter = '0;
                if (req_temp == 2'b01 || req_temp == 2'b11) begin
                    next_din_temp = din;
                    next_wait_duration_reg = wait_duration;
                    next_state_tx = WAIT_STATE_1;
                end
            end
            WAIT_STATE_1: begin
                if (wait_counter == wait_duration_reg) begin
                    next_wait_counter = '0;
                    next_state_tx = SEND_DATA;
                    tx_start = 1'b1;
                end
                else begin
                    next_wait_counter = wait_counter + 1;
                end
            end
            SEND_DATA: begin
                if (sclk_posedge) begin
                    if (data_index_tx <= (SPI_TRF_BIT-1)) begin
                        next_mosi_temp = din_temp[(SPI_TRF_BIT-1) - data_index_tx]; // MSB is sent first
                        next_data_index_tx = data_index_tx + 1;
                    end
                    else begin
                        next_din_temp = '0;
                        next_mosi_temp = '0;
                        next_data_index_tx = '0;
                        next_state_tx = WAIT_STATE_2;
                    end
                end
            end
            WAIT_STATE_2: begin
                if (wait_counter == wait_duration_reg) begin
                    next_done_temp_tx = 1'b1;
                    next_wait_counter = '0;
                    next_state_tx = IDLE_TX;
                end
                else begin
                    next_wait_counter = wait_counter + 1;
                end
            end
            default : next_state_tx = IDLE_TX;
        endcase
    end

    always_comb begin
        // Hold current values
        next_state_rx       = state_rx;
        next_done_temp_rx   = done_temp_rx;
        next_data_index_rx  = data_index_rx;
        next_dout_temp      = dout_temp;

        case(state_rx)
            IDLE_RX: begin
                next_done_temp_rx = '0;
                next_data_index_rx = '0;
                if (req_temp == 2'b10 || (req_temp == 2'b11 && tx_start)) begin
                    next_state_rx = GET_DATA;
                end
            end
            GET_DATA: begin
                if (sclk_negedge) begin
                    if (data_index_rx <= (SPI_TRF_BIT-1)) begin
                        next_data_index_rx = data_index_rx + 1;
                        next_dout_temp = {dout_temp[(SPI_TRF_BIT-2):0], miso};
                    end
                    else begin
                        next_done_temp_rx = 1'b1;
                        next_data_index_rx = '0;
                        next_state_rx = IDLE_RX;
                    end
                end
            end
            default : next_state_rx = IDLE_RX;
        endcase
    end

	assign done_tx = done_temp_tx;
	assign done_rx = done_temp_rx;
	assign mosi = mosi_temp;
	assign dout = dout_temp;
	assign sclk_en = ((state_tx == SEND_DATA) || (state_rx == GET_DATA))? 1'b1 : 1'b0; // only generate sclk when master is either sending data, receiving data or both
	assign cs = ((state_tx != IDLE_TX) || (state_rx != IDLE_RX))? 1'b0 : 1'b1; // CS is low only when some request is being executed

endmodule
