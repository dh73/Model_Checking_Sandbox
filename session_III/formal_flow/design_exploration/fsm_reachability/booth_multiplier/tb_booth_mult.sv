`timescale 1ns/1ps

module tb_booth_mult ();
   parameter W = 8;
   parameter N = $clog2(W);
   logic 		   clk, reset_n, start;
   logic [W-1:0] 	   multiplier, multiplicant;
   logic [W*2-1:0] 	   product;
   logic 		   finish;

   initial begin
      $dumpfile("test.vcd");
      $dumpvars(0,tb_booth_mult);
      #5 clk = 0;
      #10 reset_n = 1'b0;
      #5 reset_n = 1'b1;
      #5 multiplier=8'd4;
      #5  multiplicant=8'd8;
      #5 start = 1'b1;
      #900 $finish();
   end

   always #5 clk=~clk;

   booth_mult #(.W(W), .N(N)) booth_mult (.*);

endmodule // tb_booth_mult
