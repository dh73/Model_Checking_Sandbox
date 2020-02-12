// 03/21/2019
// Definition of LTSSM FSM and sub states for an upstream device
// dh
`ifndef _PIPE_PKG_
 `define _PIPE_PKG_

timeunit 1ns/1ps;

package pipe_pkg;
   /* Main LTSSM which contains the 11 states of the PCIe link training;
    In simple Gen1 linkup operation, transition will be detect -> polling -> configuration -> l0. */
   typedef enum logic [3:0] {detect, polling, configuration, l0, l0s, l1, l2, disabled, hot_reset, recovery, loopback} ltssm;
   // Detect substates that check if there's a far end termination (receiver) capable of communication.
   typedef enum logic [2:0] {idle, detect_quiet, detect_active, exit_detect} detect_sub;
   // Polling substates that stablish bit lock, symbol lock and configure lane polarity by ts1/ts2 exchange.
   typedef enum logic [1:0] {polling_active, polling_configuration, polling_compliance} polling_sub;
   // Configuration substates on which both link partners exchange ts to determine link and lane number.
   typedef enum logic [2:0] {conf_linkwidth_start, conf_linkwidth_accept, conf_lanenum_wait, conf_lanenum_accept, conf_complete, conf_idle} conf_sub;
   // When controller reach L0, configuration is complete (link is fully working).

   // Upstream data types and configurations
   // TxData/RxData
   typedef logic [15:0] pipe_width;
   // PowerDown 
   typedef enum 	logic [1:0] {P0,  // 2'b00: P0
				     P0s, // 2'b01: P0s
				     P1,  // 2'b10: P1
				     P2   // 2'b11: P2
				     } power_states;
   // RxStatus
   typedef enum 	logic [3:0] {recv_data_ok,                
				     one_skip_add,                 
				     one_skp_remove,               
				     receiver_detected,        
				     disparity_and_8b10b_err, 
				     elasctic_buffer_overflow,
				     elastic_buffer_underflow,
				     receive_disparity_error 	
				     } rxstatus_codes;
   // TS1/TS2 Ordered Sets
   typedef struct 	packed {
      pipe_width COM;
      pipe_width LINK;
      pipe_width LANE;
      pipe_width NFTS;
      pipe_width RATEID;
      pipe_width TRN;
      pipe_width TS;
   } trainig_sets;
   
   localparam [1:0] lanes  = 0;
   localparam [1:0] max_ep = 1;

   // Helpers
   // The main Frequency should be 100MHz
   // Detect.Quiet state needs a 12ms timeout
   localparam timout_12ms = 1200000;
   // A 24ms timeout for Polling.Active state
   localparam timout_24ms = 2400000;
   // For polling, link is Gen1 (2.5Gt/s), symbol time = 10b/2.5GB/s = 4ns
   // Sending 1024 TS1 (16 symbols) = 16 * 4ns * 1024 = 64us
   localparam timout_64us = 6400;   
endpackage // pipe_pkg

   // Import required datat types from package in this scope
   import pipe_pkg::pipe_width;

   //TODO: Define if architecturally, a clocked interface would work better.
interface pipe_version;
   pipe_width           TxData;
   logic [1:0] 		TxDataK;
   pipe_width           RxData;
   logic [1:0] 		RxDataK;
   logic                RxDataValid;
   logic 		RxValid;
   logic 		RxStandBystatus;		
   logic 		TxDetectRxorLpbk;
   logic 		TxDataValid;
   logic 		TxElecIdle;
   logic 		TxCompliance;
   logic 		RxPolarity;
   logic [2:0] 		PowerDown;
   logic 		Rate;
   logic 		TxDeemph;
   logic [2:0] 		TxMargin;
   logic 		TxSwing;
   logic 		PhyStatus;
   logic 		RxElecIdle;
   logic [2:0] 		RxStatus;
   logic [2:0] 		PCLK_Rate;
   logic 		RxStandby;
   logic [1:0] 		Width;
   logic                RxStandbyStatus;

   modport upstream(input  PhyStatus, RxData, RxDataK, RxDataValid, RxElecIdle, RxStandbyStatus, RxStatus, RxValid,
		    output PCLK_Rate, PowerDown, RxPolarity, RxStandby, TxCompliance, TxData, TxDataK, TxDataValid, TxDetectRxorLpbk, TxElecIdle, Width);
   
endinterface // pipe_version
`endif //  `ifndef _PIPE_PKG_
   
   
   
