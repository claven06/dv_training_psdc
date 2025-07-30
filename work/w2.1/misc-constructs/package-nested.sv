// Define a new package called X
package X;
  byte    lb     = 8'h10;
  int     word   = 32'hcafe_face;
  string  name = "X";

  function void display();
    $display("pkg=%s lb=0x%0h word=0x%0h", name, lb, word);
  endfunction
endpackage

// Define a new package called Y, use variable value inside X within Y
package Y;
  import X::*;

  byte    lb   = 8'h10 + X::lb;
  string  name = "Y";

  function void display();
    $display("pkg=%s lb=0x%0h word=0x%0h", name, lb, word);
  endfunction
endpackage

// Define a new package called Z, use variable value inside Y within Z
package Z;
  import Y::*;
  import X::*;

  byte    lb   = 8'h10 + Y::lb;
  string  name = "Z";

  function void display();
    // Note that 'word' exists in package X and not in Y, but X
    // is not directly imported here in Z, so the statement below
    // will result in a compilation error
    $display("pkg=%s lb=0x%0h word=0x%0h", name, lb, word);//require to import x

    //$display("pkg=%s lb=0x%0h", name, lb);//use this when not import x
  endfunction
endpackage

module tb;
  // import only Z package
  import Z::*;

  initial begin
    X::display();   // Direct reference X package
    Y::display();   // Direct reference Y package
    display();      // Taken from Z package because of import
  end
endmodule
