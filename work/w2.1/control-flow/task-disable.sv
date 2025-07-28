module tb;
    initial display();

    initial begin
    //after 50 time units, disable a particular named
    //block T_DISPLAY inside the task called 'display'
    #50 disable display.T_DISPLAY;
    end

    task display();
        begin: T_DISPLAY
            $display("[T=%0t] T_Task started", $time);
            #60;
            $display("[T=%0t] T_Task ended", $time);
        end

        begin: S_DISPLAY
            #10;
            $display("[T=%0t] S_Task started", $time);
            #20;
            $display("[T=%0t] S_Task ended", $time);
        end
    endtask

endmodule
