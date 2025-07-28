//
//System Verilog Package
//A SystemVerilog package offers a way to store and share data, methods, 
//properties, and parameters that can be reused across multiple modules, 
//interfaces, or programs. Packages have explicitly defined scopes that 
//exist at the same level as top-level modules, allowing all parameters 
//and enumerations to be referenced within this scope.
//
//A SystemVerilog package can be imported into the current scope using the 
//keyword import followed by the scope resolution operator ::, enabling the use 
//of their items.
//  import <package_name>::*; // Imports all items
//  import <package_name>::<item_name>; // Imports specific item
//
//wildcard import:
//When package items are imported using a wildcard, only the items that are 
//actually utilized in the module or interface are imported. Any definitions 
//and declarations in the package that are not referenced remain unimported. 
//So, an import essentially means that it is made visible.
//
//Search order
//Local definitions and declarations within a module or interface have priority 
//over any wildcard import. Similarly, an import that explicitly names specific 
//items from a package will also take precedence over a wildcard import. 
//A wildcard import essentially extends the search rules to include the package 
//when resolving an identifier. Software tools will first look for local 
//declarations (following Verilog's search rules within a module), then in any 
//packages imported with a wildcard, and finally in SystemVerilog’s $unit 
//declaration space.
//
package my_pkg;
	typedef enum bit { READ, WRITE } e_rd_wr;
endpackage

import my_pkg::*;

module tb;
  typedef enum bit { WRITE, READ } e_wr_rd;

	initial begin
        e_wr_rd  	opc1 = READ;

        //In order for the simulator to apply value from the package, 
        //the package name should be explicitly mentioned using the :: operator
        e_rd_wr  	opc2 = my_pkg::READ;
      $display ("READ1 = %0d READ2 = %0d ", opc1, opc2);
	end
endmodule
