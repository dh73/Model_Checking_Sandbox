`timescale 1ns/1ps
`default_nettype none
module booth_mult #(parameter W = 8, //default word size
	            parameter N = $clog2(W))
   (input  wire            clk, reset_n, start,
    input  wire [W-1:0]    multiplier, multiplicant,
    output logic [W*2-1:0] product,
    output logic 	   finish);
   
   logic [W-1:0] 	   mcand, acc;
   logic [N-1:0] 	   cnt;
   logic [W:0] 		   mp;
   
   typedef enum    logic [1:0] {idle, computation, right_shift} states_t;
   states_t current, next;
   
   always_ff @(posedge clk) 
     begin: state_logic
	if(~reset_n) 
	  current <= idle;
	else         
	  current <= next;
     end 
   
   always_comb 
     begin: next_state_logic
    	unique case(current)
    	  idle: 
	    begin
	       // if start we move to computation
	       // otherwise we keep in idle
    	    end
    	  
    	  computation: 
	    next = right_shift;
	  
    	  right_shift: 
	    begin
	       // if the counter is empty, we move to idle
	       // otherwise we loop in computation state
    	    end
	  
    	  default:
    	    next = idle;
    	endcase // current
     end
   
   always_ff @(posedge clk) 
     begin: output_logic
	unique case(current)
    	  idle: begin
	     unique if(start) 
	       begin
    		  mp <= {multiplier, 1'b0};
    		  mcand <= multiplicant;
    		  finish <= 1'b0;
    		  acc <= 0;
    		  cnt <= W - 1;
    	       end
	  end
	  
    	  computation: 
    	    begin
	       /* If mp[1:0] == 2'b01, we add to the acc, the value of acc plus mcand.
		  If mp[1:0] == 2'b10, we subtract to the acc, the value of the acc minus mcand.
		  Better to use a parallel construct instead of a series of comparators (if statements) */
	       unique case(mp[1:0])
		 // Your code here
		 default: ;
    	       endcase // mp[1:0]
    	    end
	  
    	  right_shift: 
	    begin
    	       {acc, mp} <= {acc[W-1], acc, mp[W:1]};
    	       cnt <= cnt - 1'b1;
    	       if(cnt==0) 
		 finish <= 1'b1;
    	    end
	  default: ;
    	endcase // mp[1:0]
     end // block: output_logic

     assign product = {acc, mp[W:1]};

   // Formal properties
   default clocking fpv_clk @(posedge clk); endclocking
   default disable iff (!reset_n);
   // Your checks here
   ap0: cover property (current == idle && start ##[1:$] finish);
endmodule
