

module fsm_short(
    output logic r, y, g,  // Red, Yellow, Green light
    input  logic clock,    // System clock
    input  logic reset     // Active-high synchronous reset
);

typedef enum {RED, GREEN, YELLOW} state_t;
state_t PS, NS;
reg [7:0] timer;  // 8-bit timer (0-255 counts)

always @(posedge clock or posedge reset) begin
    if (reset) begin
        PS <= RED;
        timer <= 0;
    end
    else begin
        PS <= NS;
        timer <= (PS != NS) ? 0 : timer + 1;
    end
end

always_comb begin
    NS = PS;  // Default: stay in current state
    case (PS)
        RED:    if (timer >= 20) NS = GREEN;
        GREEN:  if (timer >= 15) NS = YELLOW;
        YELLOW: if (timer >= 5) NS = RED;
    endcase
end

always_comb begin
    {r,y,g} = 3'b100;  // Default to RED
    case (PS)
        GREEN:  {r,y,g} = 3'b001;
        YELLOW: {r,y,g} = 3'b010;
    endcase
end

endmodule


