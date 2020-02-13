/* Control registers:
 * 1) Set the duty cycle.
 * 2) Set the divisor value
 */

`default_nettype none
module pwm_avalon_top
  (input  wire         clock, resetn,
   input  wire         read, write,
   input  wire  [31:0] writedata,
   input  wire  [0:0]  address,
   output logic [31:0] readdata,
   output logic        pwm_export);

   logic               duty_wr_strobe;
   logic               duty_rd_strobe;
   logic               dvsr_wr_strobe;
   logic               dvsr_rd_strobe;
   logic [31:0]        csr0, csr1; //csr0 for duty, csr1 for dvsr
   
   assign duty_wr_strobe = write && (address == 1'b0);
   assign duty_rd_strobe = read && (address == 1'b0);
   assign dvsr_wr_strobe = write && (address == 1'b1);
   assign dvsr_rd_strobe = read && (address == 1'b1);
	 
   // Write the value of duty or dvsr to the component
   always_ff @(posedge clock, negedge resetn) begin
      if (~resetn) begin
	 // Clear csr0 and csr1
      end
      else begin
         unique case ({duty_wr_strobe, dvsr_wr_strobe})
	   // If duty_wr_strobe, assign to csr0 the writedata input
           2'b10: csr0 <= writedata; // Is this the correct answer?
           // if dvsr_wr_strobe, assign to csr1 the writedata input
	   // <Your code here>
           default: ;
         endcase // unique case ({duty_wr_strobe, dvsr_wr_strobe})
      end
   end

   // Read data from component
   always_ff @(posedge clock, negedge resetn) begin
      if (~resetn)
        readdata <= 32'b0;
      else begin
         unique case ({duty_rd_strobe, dvsr_rd_strobe})
	   // If duty_rd_strobe, assign to readdata the csr0 value (beware, csr0 is 11 bits!)
           // So you might need to assign something to the upper 21 bits
	   // <Your code here>
	   // If dvsr_rd_strobe, assign to readdata the csr1 value
           // <Your code here>
         endcase // unique case ({duty_rd_strobe, dvsr_rd_strobe})
      end
   end

   pwm_core #(.R(10)) ucore (clock, resetn, csr0, csr1, pwm_export);

   // ========================================================================
   // Formal properties
   default clocking fpv_clk @(posedge clock); endclocking
   default disable iff (!resetn);

   // Can you describe what this lines below are doing?
   input_data_master_0: assume property (writedata[10:0]  != 11'h0);
   input_data_master_1: assume property (writedata[31:11] != 21'h0);
   
    /* Prove you can setup the duty cycle CSR from the Avalon interface.
     You can use any value here for the data to write.
     To do so, writedata should be stable, and master needs to assert write and set
     the address to 1'b0. We can assume that writedata is stable, since that is 
     Master's responsibility. */
   property write_duty_cycle;
      (write == 1'b1 && address == 1'b0 |-> ##1 csr0 == $past(writedata));
   endproperty // write_duty_cycle
   a_write_duty_cycle: cover property (write_duty_cycle);

   /* Now prove that CSR1 will have the counter divisor value iff:
      write = 1'b1 and address = 1'b1 */
   property write_divisor_value;
      (write == 1'b1 && address == 1'b1 |-> ##1 csr1 == $past(writedata));
   endproperty // write_duty_cycle
   a_write_divisor_value: cover property (write_divisor_value);

   /* Lets do something more interesting: check that the actual duty cycle
      written by the Avalon interface, is what the PWM executes */
   logic [10:0] dc_formal;
   control_writes: assume property (duty_wr_strobe |-> always nexttime[2] !duty_wr_strobe);
   
   always_ff @(posedge clock) begin
      if (~resetn)             dc_formal <= {11{1'b0}};
      else if (duty_wr_strobe) dc_formal <= writedata [10:0];
      
      if ($rose(pwm_export)) 
	dc_formal <= dc_formal - 1'b1;
   end // always_ff @ (posedge clock)
   
   /* If the dc_counter counter is not 0 when the PWM fells, then PWM is not executing duty cycle
      correctly (this is a weak cover) */
   check_duty: cover property ($rose(pwm_export) && dc_formal > 11'h0 ##1 !$fell(pwm_export));
   //=========================================================================================
endmodule // pwm_avalon_top

