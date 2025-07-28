
//System Verilog Callback
//
//In Systemverilog, a class method is written to call placeholder methods. 
//When needed, the user can extend the class and implement these placeholder 
//methods. Here, the placeholder methods are the callback methods, and the 
//calls to these methods act as callback hooks.
//
//The major benefit of callbacks is decoupling of components. 
//A verification environment, can register callbacks that can be executed 
//during the simulation without modifying the original design.
//
//
//Sample implementation:
//MyCallback class defines a virtual function callback_function().
//MyTest class has a function to register a callback and later executes 
//      the callback function when needed.
//UserCallback extends MyCallback and overrides the callback_function() method.
//The testbench registers the UserCallback object with the MyTest object and 
//      calls MyTest's execute(), which invokes the registered callback function.

//Callback Class
class MyCallback;

  virtual function void callback_function();
    // Default implementation (optional)
  endfunction

endclass

class MyTest;
  MyCallback cb;

  // 2. Registration of callback
  function void register_callback(MyCallback callback);
    cb = callback;
  endfunction

  function void execute();
    if (cb != null) begin
      cb.callback_function();
    end
  endfunction
endclass

// 3. Callback implementation
class UserCallback extends MyCallback;

  function void callback_function();
    $display("[UserCallback] User-defined callback called!");
  endfunction

endclass

module tb;

  initial begin
    MyTest        test;
    UserCallback  user_cb;

    test    = new;
    user_cb = new;

    // Register user-defined callback
    test.register_callback(user_cb);

    // 4. Execute which will invoke the callback
    test.execute();
  end
endmodule


