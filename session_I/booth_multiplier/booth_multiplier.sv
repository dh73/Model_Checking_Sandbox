`default_nettype none
module booth_multiplier #(parameter N=8, M=$clog2(N))
   (output logic [N*2-1:0] o_result,
    output logic       o_finish,
    input wire 	       i_clk, i_rst_n,
    input wire 	       i_start,
    input wire [N-1:0] i_multiplier, i_multiplicand);

   // internal signals
   typedef enum        logic [1:0] {idle, computation} states_t;
   logic [N:0] 	       mp;
   logic [N-1:0]       mcand, cnt;
   logic [N*2-1:0]     acc;
   states_t current, next;

   always_ff @(posedge i_clk) begin
      if(~i_rst_n) current <= idle;
      else         current <= next;
   end

   always_comb begin
      unique case(current)
	idle:
	  begin
	     if(i_start) next = computation;
	     else        next = idle;
	  end
	computation:
	  begin
	     if(cnt)   next = idle; // :-)
	     else      next = computation;
	  end
	default: next = idle;
      endcase // unique case (current)
   end // always_comb

   always_ff @(posedge i_clk) begin
      case(current)
	idle:
	  begin
	     o_finish <= 1'b0;
	     if(i_start) begin
		mcand <= i_multiplicand;
		mp[N:1] <= i_multiplier;
		acc <= {N{1'b0}};
		mp[0] <= 1'b0;
		cnt <= N - 1'b1;
	     end
	  end // case: idle
	
	computation:
	  begin
	     case(mp[1:0])
	       2'b10: acc <= acc - mcand;
	       2'b01: acc <= acc + mcand;
	       default:
		 acc <= acc;
	     endcase // case (mp[1:0])
	     {acc, mp} <= {acc[N-1], acc, mp[N:1]};
	     cnt <= cnt - 1'b1;
	     if(cnt == {N{1'b0}})
	       o_finish <= 1'b1;
	  end // case: computation
      endcase // case (current)   
   end // always_ff @ (posedge i_clk)
   
   assign o_result = acc;
   
   // Model checking properties
   default clocking fpv_clk @(posedge i_clk); endclocking
   default disable iff (!i_rst_n);

   // If current state is in computation and counter is full, next state should be
   // idle, from the next clock cycle.
   correct_result: assert property (current == computation && ~&cnt |-> ##1 current == idle);

endmodule // booth_mult_asm
