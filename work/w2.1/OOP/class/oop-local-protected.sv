class Base;
  local int secret;
  protected int shared;

  function void set_shared(int val);
    shared = val;
  endfunction

  function void set_secret(int val);
    secret = val;
  endfunction
endclass

class Child extends Base;

  function void try_access();
  //  secret = 42; // Compile error: not accessible
  endfunction

  function void use_shared();
    shared = shared + 1; // Legal
  endfunction

  function display();
    $display("shared=%0d", shared);
  endfunction

endclass

module tb;
    initial begin
        Base bc = new();
        Child cc = new();
    
        for (int i=0; i< 5; i++) begin
            cc.use_shared();
        end

        cc.display();
        //display("shared=%0d", shared);
    end
endmodule
