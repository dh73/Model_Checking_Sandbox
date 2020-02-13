`default_nettype none
/* A fair bus arbiter.
 * Each request from 3 masters, should be eventually granted.
 * The arbiter is fair, that means, equal number of grants needs to be
 * given.
 */
package bus_utils;
   typedef enum logic [6:0] {IDLE    = 7'b0000001,
			     MASTER1 = 7'b0000010,
			     IDLE1   = 7'b0000100,
			     MASTER2 = 7'b0001000,
			     IDLE2   = 7'b0010000,
			     MASTER3 = 7'b0100000,
			     IDLE3   = 7'b1000000} states_t;
endpackage // bus_utils
   
module bus_arbiter
  (input  wire  clk, reset, frame, irdy,
   input  wire 	req1, req2, req3,
   output logic gnt1, gnt2, gnt3);

   // Importing the user defined types
   import bus_utils::*;
   
   states_t ps, ns;
   logic 	done, gnt1_w, gnt2_w, gnt3_w;
   
   /* define glue signals */
   assign done = frame && irdy;
   
   /* state register code */
   always_ff @(posedge clk)
     begin
	if (reset)
	  ps <= IDLE;
	else
	  ps <= ns;
     end

   /* next state combinational logic */
   always_comb
     begin
	ns = IDLE;
	unique case(ps)
	  IDLE: begin
	     if (req1 == 1'b0)
	       ns = MASTER1;
	     else if (req1 == 1'b1 & req2 == 1'b0)
	       ns = MASTER2;
	     else if (req3 == 1'b0 & req1 == 1'b1)
	       ns = MASTER3;
	     else
	       ns = IDLE;
	  end

	  MASTER1: begin
	     if (done)
	       ns = MASTER1;
	     else
	       ns = IDLE1;
	  end

	  IDLE1: begin
	     if(req2 == 1'b0 )
	       ns = MASTER2;
	     else if (req3 == 1'b0 & req2 == 1'b1)
	       ns = MASTER3;
	     else if (req3 == 1'b1 & req1 == 1'b0 & req2 == 1'b1)
	       ns = MASTER1;
	     else
	       ns = IDLE1;
	  end

	  MASTER2: begin
	     if (~done)
	       ns = MASTER2;
	     else
	       ns = IDLE2;
	  end

	  IDLE2: begin
	     if (req3 == 1'b0)
	       ns = MASTER3;
	     else if (req3 == 1'b1 & req1 == 1'b0)
	       ns = MASTER1;
	     else if (req1 == 1'b1 & req2 == 1'b0)
	       ns = MASTER2;
	     else
	       ns = IDLE2;
	  end
	  
	  MASTER3: begin
	     if (~done)
	       ns = MASTER3;
	     else
	       ns = IDLE3;
	  end

	  IDLE3: begin
	     if (req1 == 1'b0)
	       ns = MASTER1;
	     else if (req1 == 1'b1 & req2 == 1'b0)
	       ns = MASTER2;
	     else if (req2 == 1'b1 & req3 == 1'b0)
	       ns = MASTER3;
	     else
	       ns = IDLE3;
	  end

	endcase // unique case (ps)
     end // always_comb
   
   assign gnt1_w = (ps == MASTER1) ? 1'b0 : 1'b1;
   assign gnt2_w = (ps == MASTER2) ? 1'b0 : 1'b1;
   assign gnt3_w = (ps == MASTER3) ? 1'b0 : 1'b1;

   // Flops at the interface level
   always_ff @(posedge clk) begin
      gnt1 <= gnt1_w;
      gnt2 <= gnt2_w;
      gnt3 <= gnt3_w;
   end
   
   // Formal properties:
   default clocking fpv_clk @(posedge clk); endclocking
   default disable iff (reset);
   
   /* Each request ~req needs to be followed by a grant ~gnt. */
   property req_follows_gnt;
      (!req1 || !req2 || !req3 |-> ##[1:$] !gnt1 || !gnt2 || !gnt3);
   endproperty // req_follows_gnt
   a_req_follows_gnt: cover property (req_follows_gnt);

   /* Show a witness (trace) for the following property:
      starting from idle state, the FSM transition to MASTERN iff ~reqN 
      is deasserted, then goes to IDLEN. For instance, this is the state
      transition of ~req1: idle ~(if req1) -> MASTER1 -> IDLE1 */
   property state_transition;
      (ps == IDLE && !req1 ##1 ps == MASTER1 ##1 ps == IDLE1);
   endproperty // state_transition
   a_state_transition: cover property (state_transition);
   
endmodule // bus_arbiter
