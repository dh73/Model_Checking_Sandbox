`default_nettype none
package test;
   localparam WIDTH=4;
   typedef logic [WIDTH-1:0] size_t;
endpackage // test

   import test::*;
   
module timer
  (input wire i_clk, i_rstn, i_heartbeat,
   output 	size_t count,
   output logic timeout);

   var size_t counter_ps;
   
   initial counter_ps = 0;
   // Sequential logic
   always_ff @(posedge i_clk) begin
      if (~i_rstn || i_heartbeat) 
	counter_ps <= {WIDTH{1'b0}};
      else if (~&counter_ps)         
	counter_ps <= counter_ps + 1'b1;
   end
   // Combinational logic 
   assign count = counter_ps;
   assign timeout =&counter_ps;

   // Formal properties
   default clocking fpv_clk @(posedge i_clk); endclocking
   default disable iff (!i_rstn);
   
   constraint_hb: assume property (i_heartbeat == 1'b0);
   timeout_reached: assert property (count != 4'd0 && !timeout |-> count < 4'd10);
endmodule // timer


