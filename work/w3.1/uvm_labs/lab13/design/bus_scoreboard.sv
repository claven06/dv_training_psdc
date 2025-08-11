class bus_scoreboard extends uvm_component;
    `uvm_component_utils(bus_scoreboard)

    // Use implementation port to receive transactions
    uvm_analysis_imp #(bus_transaction, bus_scoreboard) scb_imp;

    int passed_count = 0;
    int failed_count = 0;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        scb_imp = new("scb_imp", this);
    endfunction

    // This will be called when transactions arrive
    function void write(bus_transaction tr);
        if (tr.write == 1 && tr.addr[7:4] == 4'hA) begin
            passed_count++;
            `uvm_info("SCOREBOARD", $sformatf("PASS: addr=0x%2h, data=0x%8h, write=%0b", tr.addr, tr.data, tr.write), UVM_MEDIUM)
        end else begin
            failed_count++;
            `uvm_error("SCOREBOARD", $sformatf("FAIL: addr=0x%2h, data=0x%8h, write=%0b ================", tr.addr, tr.data, tr.write))
        end
    endfunction

    function void report_phase(uvm_phase phase);
        `uvm_info("SCOREBOARD", $sformatf("Test Results: Passed=%0d Failed=%0d", passed_count, failed_count), UVM_NONE)
    endfunction
endclass

