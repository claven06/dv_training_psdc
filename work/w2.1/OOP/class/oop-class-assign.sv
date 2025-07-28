class myClass;
    bit [31:0] data;
endclass

module test;
    myClass ClassA, ClassB;

    initial begin
        ClassA = new();
        ClassA.data = 'hcafe;

        ClassB = ClassA; // assign ClassA to ClassB
        $display("ClassA.data = %0h", ClassA.data);
        $display("ClassB.data = %0h", ClassB.data);

        ClassB.data = 'habcd;
        $display("ClassA.data = %0h", ClassA.data);
        $display("ClassB.data = %0h", ClassB.data);
    end
endmodule

