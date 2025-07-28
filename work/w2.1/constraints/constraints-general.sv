class myClass;
      rand bit [3:0] min, typ, max;
      rand bit [3:0] fixed;

      constraint my_range { 3 < min;
                            typ < max;
                            typ > min;
                            max < 14; }

      constraint c_fixed { fixed == 5; }

      function string display ();
        return $sformatf ("min=%0d typ=%0d max=%0d fixed=%0d", min, typ, max, fixed);
      endfunction

endclass

    module tb;
       initial begin
          for (int i = 0; i < 10; i++) begin
             myClass cls = new ();
             cls.randomize();
             $display ("itr=%0d %s", i, cls.display());
          end
       end
    endmodule
