`default_nettype wire
module regfile #(parameter ADDRW=2, DATAW=2)
   (input  wire  i_clk, i_wen,
    input  wire  [DATAW-1:0]  i_wdata,
    input  wire  [ADDRW-1:0]  i_waddr, i_raddr,
    output logic [DATAW-1:0]  o_rdata);
   
   // Register file
   var logic [DATAW-1:0]      regfile [0:2**ADDRW-1];
   
   always_ff @(posedge i_clk) begin
      if (i_wen)
	regfile [i_waddr] <= i_wdata;
   end
   assign o_rdata = regfile [i_raddr];
endmodule // regfile
