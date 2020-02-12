`default_nettype none

`define SYNC_RSTN_EN_MFF(CLK, RSTN, EN, IN, OUT) \
   always_ff @(posedge CLK) begin \
      if (~RSTN) OUT <= 1'b0; \
        else begin \
           if (EN) \
             OUT <= IN; \
         end \
   end

package counter_formal_pkg;
   localparam WIDTH=32;
   typedef logic [WIDTH-1:0] uint32_t;
endpackage // counter_formal_pkg

module counter_formal
  (input wire i_clk, i_rstn, i_en,
   output counter_formal_pkg::uint32_t o_q);

   // Internal signal declaration
   var counter_formal_pkg::uint32_t count_ps;
   counter_formal_pkg::uint32_t count_ns;
   logic  max_count;

   // Combinational Logic functions
   assign count_ns = count_ps + 1'b1;
   assign max_count = &count_ps;
   assign o_q = count_ps;

   // Sequential logic functions
   `SYNC_RSTN_EN_MFF (i_clk, i_rstn, i_en, count_ns, count_ps)

   // Formal Constructs
   default clocking fpv_clk @(posedge i_clk); endclocking // Default clock for concurrent assertions
   default disable iff (!i_rstn); // Default disable clause for model checking

   wrong_assumption: assume property (count_ps < 32'hFFFFFFFE);
   counter_overflow: assert property (i_en && o_q == 32'hFFFFFFFF |-> ##1 o_q == 32'h00000000);
endmodule // counter_formal
