`default_nettype none
module fifo_top #(parameter ADDRW=4, DATAW=8)
   (input  wire              i_clk, i_rstn,
    input  wire 	     i_wr, i_rd,
    input  wire [DATAW-1:0]  i_wdata,
    output logic 	     o_empty, o_full, 
    output logic 	     o_almost_empty, o_almost_full, 
    output logic [2**ADDRW-1:0] o_wordcount,
    output logic [DATAW-1:0]    o_rdata);

   // Helpers
   localparam ALMOST_EMPTY = (2**ADDRW)/4;
   localparam ALMOST_FULL  = 3*(ALMOST_EMPTY);
   
   // Connectivity logic
   logic [DATAW-1:0] 	     w_waddr, w_raddr;
   logic 		     w_wen;
   assign w_wen = i_wr & ~o_full;

   // Child modules instantiation
   fifo_controller 
     #(.W(DATAW)) ctrl (.*,
			.o_waddr(w_waddr),
			.o_raddr(w_raddr));
   
   regfile
     #(.ADDRW(ADDRW), .DATAW(DATAW)) dp (.*,
					 .i_wen(w_wen),
					 .i_waddr(w_waddr),
					 .i_raddr(w_raddr));

   // Status extension logic
   var logic [2**ADDRW-1:0]  wordcount_c;
   logic [2**ADDRW-1:0]      wordcount_n;
   logic 		     increase_count, decrease_count;
   
   always_ff @(posedge i_clk) begin
      if (i_rstn)
	wordcount_c <= 0;
      else
	wordcount_c <= wordcount_n;
   end
   assign increase_count = ~o_full & i_wr;
   assign decrease_count = ~o_empty & i_rd;
   assign wordcount_n    = (increase_count) ? wordcount_c + 1'b1 :
			   (decrease_count) ? wordcount_c - 1'b1 :
			   wordcount_c;
   assign o_wordcount    = wordcount_c;
   assign o_almost_full  = (wordcount_c == ALMOST_FULL-1);
   assign o_almost_empty = (wordcount_c == ALMOST_EMPTY-1);
endmodule // fifo_top
