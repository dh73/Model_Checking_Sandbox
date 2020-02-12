`default_nettype none
module fifo_chk #(parameter W = 8)
   (input wire         i_clk, i_rstn,
    input wire 	       i_wr, i_rd,
    input wire 	       o_full, o_empty,
    input wire [W-1:0] o_waddr, o_raddr);
   
   default clocking cb_fpv @(posedge i_clk); endclocking
   default disable iff (!i_rstn);

`define MODE cover
   
   // Properties for FPV
   // Sanity Properties
   /* If no operation is requested, read pointer and write pointer should
      remain unchanged */
   property no_op_and_write;
      (!i_wr |-> ##1 $stable(o_waddr));
   endproperty // no_op_and_write
   a_no_op_and_write: `MODE property (no_op_and_write);
   
   property no_op_and_read;
      (!i_rd |-> ##1 $stable(o_raddr));
   endproperty // no_op_and_read
   a_no_op_and_read: `MODE property (no_op_and_read);
   
   /* Iff the fifo is not empty, in every read operation, read pointer 
      should increase by 1 */ 
      //--- NOTE: Beware when using past! (what happens when the value of the past is full?)
      // 8'hFF + 1'b1 -> 8'h00 but that is an overflow
   property read_no_empty;
      (!o_empty && o_raddr != {W{1'b1}} && i_rd |-> ##1 $past(o_raddr)+1'b1);
   endproperty // read_no_empty
   a_read_no_empty: `MODE property (read_no_empty);

   /* Iff the fifo is not full, in every write operation, write pointer
      should increase by 1 */
   property write_no_full;
      (!o_full && o_waddr != {W{1'b1}} && i_wr && !(o_raddr == o_waddr) |-> ##1 $past(o_waddr)+1'b1);
   endproperty // write_no_full
   a_write_no_full: `MODE property (write_no_full);
   
   /* Both read and write operations at the same time, should be
      serviced */
   property read_write;
      (i_wr && i_rd &&  o_raddr != {W{1'b1}} &&  o_waddr != {W{1'b1}} |-> ##1 $past({o_waddr, o_raddr})+1'b1);
   endproperty // read_write
   a_read_write: `MODE property (read_write);
   
   // Interesting properties
   /* If a read operation is requested, but the fifo is empty,
      read pointer should not underflow */
   property read_empty;
      (o_empty && i_rd &&  o_raddr != {W{1'b1}} |-> ##1 $stable(o_raddr));
   endproperty // read_empty
   a_read_empty: `MODE property (read_empty);
 
   /* If a write operation is requested, and the fifo is full,
      the fifo sould drop that request (i.e., not accept it) */
   property write_full;
      (o_full && i_wr |-> ##1 $stable(o_waddr));
   endproperty // write_full
   a_write_full: `MODE property (write_full);

   /* Write addr == Read addr is only possible if fifo is either
      empty or full */
   property same_addr_op_empty;
      (!o_empty ##1 o_empty |-> $past(o_raddr==o_waddr));
   endproperty // same_addr_op
   a_same_addr_op_empty: `MODE property (same_addr_op_empty);

   property same_addr_op_full;
      (!o_full ##1 o_full |-> $past(o_raddr==o_waddr));
   endproperty // same_addr_op
   a_same_addr_op_full: `MODE property (same_addr_op_full);
      
   /* The write pointer is never stuck */
   property wr_no_stuck;
      (!o_full && !o_empty && o_waddr < {W{1'b1}} |-> ##1 $past(o_waddr) + 1'b1);
   endproperty // wr_no_stuck
   a_wr_no_stuck: `MODE property (wr_no_stuck);
 
   /* The read pointer is never stuck */
   property rd_no_stuck;
      (!o_full && !o_empty && o_raddr < {W{1'b1}} |-> ##1 $past(o_raddr) + 1'b1);
   endproperty // rd_no_stuck
   a_rd_no_stuck: `MODE property (rd_no_stuck);

   /* The fifo is eventually full */
   property fifo_full;
      !o_full |-> ##[1:$] o_full;
   endproperty // fifo_full
   a_fifo_full: `MODE property (fifo_full);
endmodule // fifo_chk

bind fifo_controller fifo_chk #(.W(W)) checker_ins (.*);


