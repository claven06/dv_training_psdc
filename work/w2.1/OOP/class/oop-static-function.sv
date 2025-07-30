//
//A static method follows all class scoping and access rules, but the only 
//difference being that it can be called outside the class even with no class 
//instantiation. A static method has no access to non-static members but it 
//can directly access static class properties or call static methods of the 
//same class. Also static methods cannot be virtual. Static function calls 
//using class names need to be made through the scope operator ::.
//
class Packet;
	static int ctr=0;
    bit [1:0] mode; //add in a non-static member called mode and try to call 
                    //that from our static function.

   function new ();
      ctr++;
   endfunction

	static function get_pkt_ctr ();
        begin
            $display ("ctr=%0d", ctr);

            //It's not allowed and will result in a compilation error.
		    //$display ("ctr=%0d mode=%0d", ctr, mode);
        end                                   
	endfunction

endclass

module tb;
	Packet pkt [6];
	initial begin
		for (int i = 0; i < $size(pkt); i++) begin
			pkt[i] = new;
		end
		Packet::get_pkt_ctr(); 	// Static call using :: operator
		pkt[5].get_pkt_ctr(); 	// Normal call using instance
	end
endmodule
