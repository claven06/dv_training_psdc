module tb;
    bit [3:0][7:0] m_data; // A Multi Dimentional Packed Array, 4 bytes

    initial begin
        // 1. Assign a value to the m_data 
        m_data = 32'hface_cafe;

        $display ("m_data = 0x%0h", m_data);

        // 2. Iterate through each segment of the m_data and print value
        for (int i = 0; i < $size(m_data); i++) begin
            $display ("m_data[%0d] = %b (0x%0h)", i, m_data[i], m_data[i]);
        end
    end
endmodule
