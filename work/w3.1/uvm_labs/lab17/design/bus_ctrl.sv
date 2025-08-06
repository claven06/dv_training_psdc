module bus_ctrl (
    input logic clk,
    input logic reset_n,
    
    // Bus interface signals
    input logic [7:0] addr,
    input logic [31:0] wdata,
    output logic [31:0] rdata,
    input logic write,
    input logic valid,
    output logic ready
);
    
    // Memory array (256 addresses x 32 bits)
    logic [31:0] mem[256];
    
    // Control registers
    logic [31:0] control_reg;
    logic [31:0] status_reg;
    
    // Internal signals
    logic addr_valid;
    logic operation_complete;
    
    // Address decoding
    always_comb begin
        addr_valid = 1'b1;
        
        // Check for reserved addresses
        if (addr[7:4] == 4'hF) begin
            addr_valid = 1'b0;  // Reserved address space
        end
    end
    
    // Main operation handling
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            rdata <= 32'h0;
            ready <= 1'b0;
            control_reg <= 32'h0;
            status_reg <= 32'h0;
            
            // Initialize memory with zeros
            foreach (mem[i]) begin
                mem[i] <= 32'h0;
            end
        end
        else begin
            ready <= 1'b0;
            operation_complete <= 1'b0;
            
            if (valid && addr_valid) begin
                if (write) begin
                    // Write operation
                    case (addr[7:4])
                        4'hA: control_reg <= wdata;  // Control register at 0xA0-0xAF
                        default: mem[addr] <= wdata; // Memory write
                    endcase
                end
                else begin
                    // Read operation
                    case (addr[7:4])
                        4'hA: rdata <= control_reg;  // Control register read
                        4'hB: rdata <= 12'hBAD;   // Status register read
                        default: rdata <= mem[addr]; // Memory read
                    endcase
                end
                
                ready <= 1'b1;
                operation_complete <= 1'b1;
                
                // Update status register
                status_reg[31] <= operation_complete;
                status_reg[7:0] <= addr;
            end
            else if (valid && !addr_valid) begin
                // Invalid address access
                ready <= 1'b1;
                status_reg[30] <= 1'b1;  // Error flag
            end
        end
    end
    
    /*/ Coverage points (optional)
    covergroup bus_cg @(posedge clk);
        addr_cp: coverpoint addr {
            bins low_addr = {[0:127]};
            bins high_addr = {[128:255]};
        }
        write_cp: coverpoint write;
        addr_x_write: cross addr_cp, write_cp;
    endgroup
    
    bus_cg cg = new();
    
    always @(posedge clk) begin
        if (valid) cg.sample();
    end
    */
endmodule
