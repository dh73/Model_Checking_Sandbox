`default_nettype none
module fifo_controller #(parameter W = 8)
   (input  wire          i_clk, i_rstn,
    input  wire 	 i_wr, i_rd,
    output logic 	 o_full, o_empty,
    output logic [W-1:0] o_waddr, o_raddr);

   var logic [W-1:0] 	 w_ptr_c, r_ptr_c;
   var logic 		 empty_c, full_c;
   logic [W-1:0] 	 w_ptr_n, r_ptr_n;
   logic 		 empty_n, full_n;
   
   always_ff @(posedge i_clk) begin
      if (~i_rstn) begin
	 w_ptr_c <= {W{1'b1}};
         r_ptr_c <= {W{1'b1}};
         empty_c <= 1'b1;
         full_c   <= 1'b0;
      end
      else begin
	 w_ptr_c <= w_ptr_n;
	 r_ptr_c <= r_ptr_n;
	 empty_c <= empty_n;
	 full_c  <= full_n;
      end
   end

   always_comb begin
      r_ptr_n = r_ptr_c;
      w_ptr_n = w_ptr_c;
      empty_n = empty_c;
      full_n  = full_c;
      
      unique case ({i_wr, i_rd})
	2'b00: begin // nop
	   r_ptr_n = r_ptr_c;
	   w_ptr_n = w_ptr_c;
	end
	
	2'b01: begin // read (pop)
	   if (~empty_c) begin
	      r_ptr_n = r_ptr_n + 1'b1;
	      full_n = 1'b0;
	      if (r_ptr_c == w_ptr_c)
		empty_n = 1'b1;
	   end
	end
	
	2'b10: begin // write (push)
	   if (~full_c) begin
	      w_ptr_n = w_ptr_c + 1'b1;
	      empty_n = 1'b0;
	      if (r_ptr_c == w_ptr_c)
		full_n = 1'b1;
	   end
	end
	
	2'b11: begin // read and write
	   // Here is a bug
	   if (~full_c && ~empty_c) begin // I've added this line
	      r_ptr_n = r_ptr_c + 1'b1;
	      w_ptr_n = w_ptr_c + 1'b1;
	   end
	end
      endcase // {i_wr, i_rd}
   end // always_comb
   
   assign o_full  = full_c;
   assign o_empty = empty_c;
   assign o_waddr = w_ptr_c;
   assign o_raddr = r_ptr_c;
endmodule
