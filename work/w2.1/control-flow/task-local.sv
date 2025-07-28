module tb;
    des u0();

    initial begin
        #1
        $display("[T=%0t]In module tb",$time);
        u0.display();   //Task is not visible in the module 'tb'
    end
endmodule

module des;
    initial begin
        $display("[T=%0t]In module des",$time);
        display();  //Task definition is local to the module
    end

    task display();
        $display("[T=%0t des.task] Hello World!",$time);
    endtask
endmodule
