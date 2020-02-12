`default_nettype none
module gp_timer #(parameter TIMEOUT = 10, [0:0] RST_LVL = 0)
   (output logic  o_timeout,
    input  wire   i_clk,
    input  wire   i_start,
    input  wire   i_rst);
   
   // Handling reset source polarity
   logic 		     w_rst_n;
   assign w_rst_n = i_rst ^ RST_LVL;
   
   // Internal signals
   localparam WIDTH = ($clog2(TIMEOUT));
   var logic [WIDTH-1:0]     counter_ps;
   logic 		     tick_w;
   
   always_ff @(posedge i_clk) begin
      if(~w_rst_n || i_start) 
	counter_ps <= {WIDTH{1'b0}};
      else begin
	 if ((~&counter_ps) && (counter_ps != TIMEOUT-1))
	   counter_ps <= counter_ps + 1'b1;
      end
   end
   assign o_timeout = counter_ps == TIMEOUT-1;

   // Formal Properties
   // Default clauses
   default clocking fpv_clk @(posedge i_clk); endclocking
   default disable iff (~i_rst);

   // Visualize
   /* Since I pretend to abstract this timer anyway, I just need to check,
      for now, that a o_timeout can be toggled and visual inspect that the
      counter_ps is in the correct value */
   //toggling_timeout: cover property (o_timeout == 1'b0 ##1 o_timeout == 1'b1);
endmodule // gp_timer
`default_nettype wire
