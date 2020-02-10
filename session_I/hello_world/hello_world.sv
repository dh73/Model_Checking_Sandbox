`default_nettype none
module hello_world
  (input wire i_clk, i_rstn,
   output logic       o_full,
   output logic [7:0] o_result);

   always_ff @(posedge i_clk) begin
      if (~i_rstn) o_result <= 8'b0;
      else if (~&o_result) o_result <= o_result + 1'b1;
   end
   assign o_full = &o_result[8];
   
   // Formal properties
   default clocking fpv_clk @(posedge i_clk); endclocking
   default disable iff (!i_rstn);

   // If counter is full, o_full will be asserted and counter will remain
   // stable starting the next clock cycle.
   ap_full_stable: assert property (&o_result |-> ##1 o_full && $stable(o_result));
endmodule // hello_world
