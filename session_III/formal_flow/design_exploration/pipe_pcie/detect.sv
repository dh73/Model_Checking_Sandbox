// TODO: Don't forget to synchronize phystatus and rxstatus (double ff)
`default_nettype none
module detect
  (input  wire        i_core_clk,
   input  wire 	      i_start_detect,
   input  wire 	      PhyStatus,
   input  wire [2:0]  RxStatus,
   input  wire 	      RxElecIdle,
   input  wire 	      i_rstn,
   output logic [2:0] PowerDown,
   output logic       TxDetectRxorLpbk,
   output logic       o_ready, o_done);
   
   // Import data types, parameters and signals from the package
   import pipe_pkg::*;

   // Internal signals
   detect_sub DETECT_ns, DETECT_ps;

   //rxstatus_codes RxCodes;
   logic 	      w_timeout_12ms;
   logic 	      w_start;
   logic 	      w_rst;
   logic 	      old_PhyStatus = 1'b0;
   logic 	      old_TxDetectRxorLpbk = 1'b0;
   logic 	      PhyStatus_edge, TxDetectRxorLpbk_edge;
   
   // Timer instance
   gp_timer #(.TIMEOUT(timout_12ms), .RST_LVL(0)) 
   gp_timer_inst
     (.o_timeout(w_timeout_12ms),
      .i_clk(i_core_clk),
      .i_start(w_start),
      .i_rst(w_rst));
   
   // Store PhyStatus to detect when is asserted
   always_ff @(posedge i_core_clk) begin: edge_detection_on_phystatus
      old_PhyStatus <= PhyStatus;
   end
   assign PhyStatus_edge = PhyStatus & ~ old_PhyStatus;

   // Same for TxDetect
   always_ff @(posedge i_core_clk) begin: edge_detection_on_txdetect
      old_TxDetectRxorLpbk <= TxDetectRxorLpbk;
   end
   assign TxDetectRxorLpbk_edge = ~ TxDetectRxorLpbk &  old_TxDetectRxorLpbk;

   // Detect FSM
   always_ff @(posedge i_core_clk) begin: fsm
      if(~i_rstn)
	DETECT_ps <= idle;
      else
	DETECT_ps <= DETECT_ns;
   end
   
   always_comb begin: next_state_logic
      DETECT_ns = DETECT_ps;
      unique case(DETECT_ps)
	/* This idle state will be used for the 
	 controller logic. It introduces one cycle
	 latency in the first execution*/
	idle: begin
	   if(i_start_detect)
	     DETECT_ns = detect_quiet;
	   else
	     DETECT_ns = idle;
	end
	/* The controller will exit to Detect.Active iff:
	 1) PowerState is  P1.
	 2) PhyStatus is de-asserted on all lanes that are active.
	 3) And 12ms timeout happens. */
	detect_quiet: begin
	   if( PhyStatus & (~RxElecIdle & w_timeout_12ms))
	     DETECT_ns = detect_active;
	   else
	     DETECT_ns = detect_quiet;
	end
	/* Detect.Active is the state on which the controller performs
	 receiver detection (i.e., if there is a far end termination
	 capable of send/receive data.
	 Detect.Active will exit to polling when all unconfigured lanes 
	 have detected a receiver. Will return to Detect.quiet iff:
	 1) Not all unconfigured lanes present detected a receiver.
	 2) No receiver detected on any lane.
	 3) Detection errors (retry).*/
	detect_active: begin
	   // Sampling on PhyStatus
	   if(PhyStatus) begin
	      unique case(RxStatus) inside
		receiver_detected: begin 
		   if (~TxDetectRxorLpbk_edge) DETECT_ns = exit_detect;
		   else                        DETECT_ns = detect_quiet;
		end
		/* There's no control of the mac errors yet, so
	         if that happens, send the DETECT FSM to Detect.Quiet again */
		default:
		  DETECT_ns = detect_quiet;
	      endcase // unique case (RxStatus inside RxCodes)
	   end
	end
	// Exit Detect substates.
	exit_detect:
	  DETECT_ns = idle;
	default:
	  /* Most linter/synthesis tool shows warnings if not default
	   is defined, even when you explicity defines the next state logic 
	   for all undefined brances, so a comma here do the work */
	  ;
      endcase // unique case (DETECT_ns)
   end // block: next_state_logic

   always_ff @(posedge i_core_clk) begin: output_logic
      // TODO: Manage PowerDown
      PowerDown <= P1;
      w_start <= 1'b0;
      w_rst <= 1'b0;
      unique case(DETECT_ps)
	idle: {o_ready, o_done} <= {1'b1, 1'b0};
	detect_quiet: {w_start, w_rst} <= {1'b1, 1'b1};
	/* Assert txDetectRxorLpbk and wait for PhyStatus 
	 to drive the detection code */
	detect_active: begin
	   if(PhyStatus_edge)
	     TxDetectRxorLpbk <= 1'b1;
	   else
	     TxDetectRxorLpbk <= 1'b0; 
	end
	exit_detect: begin
	   {o_ready, o_done} <= {1'b0, 1'b1};
	   TxDetectRxorLpbk <= 1'b1;
	end
	default:
	  ;
      endcase // unique case (DETECT_ns)
   end // block: output_logic
   
   default clocking PCLK @(posedge i_core_clk); endclocking
   default disable iff (!i_rstn);

   c0_detect_quiet_to_detect_active: cover property(DETECT_ps==detect_quiet & !PhyStatus & (~RxElecIdle & w_timeout_12ms) ##1 DETECT_ps==detect_active);
   c1_receiver_detected: cover property(DETECT_ps==detect_active && TxDetectRxorLpbk==1'b1 && RxStatus== 3'b011 && PhyStatus==1'b1 ##1 
   					DETECT_ps==exit_detect   && TxDetectRxorLpbk==1'b0 && PhyStatus==1'b0);
endmodule // detect
`default_nettype wire
