//This task is outside all modules
task display();
    $display("[task] Hello World!",);
endtask

module des;
    initial begin
        display();
    end
endmodule
