class myClass;
	rand bit [2:0] typ1;
	rand bit [2:0] typ2;

    //:= the weight is the same for every specified value in the range
	constraint dist1 {typ1 dist { 0:=20, [1:5]:=50, 6:=40, 7:=10};}
    //:/ the weight is to be equally divided between all the values in the range
	constraint dist2 {typ2 dist { 0:/20, [1:5]:/50, 6:/40, 7:/10};}

endclass

module tb;
	initial begin
		for (int i = 0; i < 10; i++) begin
			myClass cls = new ();
			cls.randomize();
			$display ("itr=%0d typ1=%0d typ2=%0d", i, cls.typ1, cls.typ2);
		end
	end
endmodule

//dist1: note that 1 through 5 has appeared more than 0, 6 or 7 because they
//       have a higher weight and are chosen more often
//dist2: note that 6 has appeared more than the others because it has the 
//       highest weight
