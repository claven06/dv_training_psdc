/* this is first line
 * this is 2nd line
//* this is another first line of new comment
 * this is 2nd line of new comment
 */
module tbench_top;
  reg [7:0]  m_var1;
  reg [15:0] m_var2;

  real  pi; // Declared to be of type real
  real  freq;

  // "enum_light" is a new data-type with three valid values: RED, YELLOW and
  // GREEN
  typedef enum {RED,YELLOW,GREEN} enum_light;
  // Declare a variable of type "enum_light" that can store RED, YELLOW and
  // GREEN
  enum_light light;

  initial begin
    m_var1 = '1;
    m_var2 = '1;

    $display ("\n=== datatype reg ==");
    $display("m_var1=0x%0h  m_var2=0x%0h", m_var1, m_var2);

    m_var1 = 'hz;
    m_var2 = 'h1;

    $display("m_var1=0x%0h  m_var2=0x%0h", m_var1, m_var2);
    $display("=== datatype reg ==");

    pi   = 3.14;    // Store floating point number
    freq = 1e6;     // Store exponential number

    $display ("\n=== datatype real ==");
    $display ("Value of pi = %f", pi);
    $display ("Value of pi = %0.3f", pi);
    $display ("Value of freq = %0d", freq);

    // This does not work - Radix must be specified !
    //m_var1 = 'F0;
    //m_var2 = 'cafe;
    $display ("=== datatype real ==");

  // Strings can be split into multiple lines [for visual appeal] by the using 
  // "" and , characters
  // This does not split the string into multiple lines in the output
  // Result: Penang is an awesome place.So energetic and vibrant.
    $display ("\n=== datatype strings ==");
    $display ("Penang is an awesome place. ",
                "So energetic and vibrant.");

  // Strings can be split to be displayed in multiple lines using \n
  /* Result:
  Penang is an awesome place.
  So energetic and vibrant.
  */
    $display ("Penang is an awesome place. \n",
                "So energetic and vibrant.");
    $display ("=== datatype strings ==");

  // Assign RED to the enumerated variable
    light = RED;

    $display ("\n=== datatype typedef enum ==");
  // Display string value of the variable
    $display ("light = %s", light.name);
    $display ("=== datatype typedef enum ==");

  end

endmodule
