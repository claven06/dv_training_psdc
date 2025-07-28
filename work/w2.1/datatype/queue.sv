module tb;
    string fruits[$] = {"apple", "pear", "mango", "banana"};

    initial begin
        $display("==========================================================");
        // size() - Gets size of the given queue
        $display ("Number of fruits=%0d, fruits=%p", fruits.size(), fruits);

        // insert() - Insert an element to the given index
        fruits.insert (1, "peach");
        $display ("Insert peach to index 1, size=%0d fruits=%p", fruits.size(), fruits);

        // delete() - Delete element at given index
        fruits.delete (3);
        $display ("Delete index 3, mango, size=%0d fruits=%p", fruits.size(), fruits);

        // pop_front() - Pop out element at the front
        $display ("Pop out %s, size=%0d fruits=%p", fruits.pop_front(), fruits.size(), fruits);

        // push_front() - Push a new element to front of the queue
        fruits.push_front("apricot");
        $display ("Push front, apricot, size=%0d fruits=%p", fruits.size(), fruits);

        // pop_back() - Pop out element from the back
        $display ("Pop back %s, size=%0d fruits=%p", fruits.pop_back(), fruits.size(), fruits);

        // push_back() - Push element to the back
        fruits.push_back("plum");
        $display ("Push back, plum, size=%0d fruits=%p", fruits.size(), fruits);
        $display("==========================================================");
    end
endmodule
