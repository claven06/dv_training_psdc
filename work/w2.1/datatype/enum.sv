  typedef enum bit [1:0] {REDLIGHT, YELLOWLIGHT, GREENLIGHT} e_light;

  // name : The next number will be associated with name starting from 0
  // GREEN = 0, YELLOW = 1, RED = 2, BLUE = 3
  typedef enum {GREEN, YELLOW, RED, BLUE} color_set_1;

  // name = C : Associates the constant C to name
  // MAGENTA = 2, VIOLET = 7, PURPLE = 8, PINK = 9
  typedef enum {MAGENTA=2, VIOLET=7, PURPLE, PINK} color_set_2;

  // name[N] : Generates N named constants : name0, name1, ..., nameN-1
  // BLACK0 = 0, BLACK1 = 1, BLACK2 = 2, BLACK3 = 3
  typedef enum {BLACK[4]} color_set_3;

  // name[N] = C : First named constant gets value C and subsequent ones
  // are associated to consecutive values
  // RED0 = 5, RED1 = 6, RED2 = 7
  typedef enum {RED[3] = 5} color_set_4;

  // name[N:M] : First named constant will be nameN and last named
  // constant nameM, where N and M are integers
  // YELLOW3 = 0, YELLOW4 = 1, YELLOW5 = 2
  typedef enum {YELLOW[3:5]} color_set_5;

  // name[N:M] = C : First named constant, nameN will get C and
  // subsequent ones are associated to consecutive values until nameM
  // WHITE3 = 4, WHITE4 = 5, WHITE5 = 6
  typedef enum {WHITE[3:5] = 4} color_set_6;

module tb;
  e_light light;
  // Create new variables for each enumeration style
  color_set_1 color1;
  color_set_2 color2;
  color_set_3 color3;
  color_set_4 color4;
  color_set_5 color5;
  color_set_6 color6;

  initial begin
    color1 = YELLOW; $display ("color1 = %0d, name = %s", color1, color1.name());
    color2 = PURPLE; $display ("color2 = %0d, name = %s", color2, color2.name());
    color3 = BLACK3; $display ("color3 = %0d, name = %s", color3, color3.name());
    color4 = RED1;   $display ("color4 = %0d, name = %s", color4, color4.name());
    color5 = YELLOW3;$display ("color5 = %0d, name = %s", color5, color5.name());
    color6 = WHITE4; $display ("color6 = %0d, name = %s", color6, color6.name());

    // Assign current value of color to YELLOW
    color1 = YELLOW;

 	// Name of the current enum
    $display ("\ncurrent color.name()  = %s" , color1.name());
    // First value is GREEN = 0
    $display ("color.first() = %0d, name = %s", color1.first(), color1.first().name());
    // Last value is BLUE = 3
    $display ("color.last()  = %0d, name = %s", color1.last(), color1.last().name());
 	// Next value is RED = 2
    $display ("color.next()  = %0d, name = %s", color1.next(), color1.next().name());
 	// Previous value is GREEN = 0
    $display ("color.prev()  = %0d, name = %s", color1.prev(), color1.prev().name());
 	// Total number of enum = 4
    $display ("color.num()   = %0d\n", color1.num());

 	light = GREENLIGHT;
  	$display ("light = %s", light.name());

  	// Invalid because of strict typing rules
  	light = 0;
  	$display ("light = %s", light.name());

  	// OK when explicitly cast
    light = e_light'(1);
  	$display ("light = %s", light.name());

  	light = GREENLIGHT;
    // OK. light is auto-cast to integer
    if (light == REDLIGHT | light == 2)
    	$display ("light is now %s", light.name());

  end
endmodule
