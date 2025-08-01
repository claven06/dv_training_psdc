module tb_halfAdder;
  
  reg  a, b;
  wire sum, carry;
  
  halfAdder dut_halfAdder(a,b,sum,carry);
  
  initial {a,b} = 2'b0;
  
  typedef struct packed {
      bit a;
      bit b;
  } my_struct_t;

  my_struct_t data[4];

  initial begin    
      data[0] = '{0,0};
      data[1] = '{0,1};
      data[2] = '{1,0};
      data[3] = '{1,1};
  end
  
  always begin
//    #5 {a,b} = $random;

    for (int i=0; i < 4; i++) begin
        #5 {a,b} = data[i];
    end

    #5 $finish;
  end
  
  initial begin
  //Monitor signals
  $monitor("Time=%0d\na = %0d + b = %0d\n---------\ncarry = %0d sum = %0d \
            \n",$time, a,b,carry,sum);
 
  $fsdbDumpfile("fsdbDump.fsdb");
  $fsdbDumpvars;

//	#100 $finish;
  end
    
  
endmodule 
