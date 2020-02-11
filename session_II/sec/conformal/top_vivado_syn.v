// Copyright 1986-2019 Xilinx, Inc. All Rights Reserved.
// --------------------------------------------------------------------------------
// Tool Version: Vivado v.2019.2 (lin64) Build 2700185 Thu Oct 24 18:45:48 MDT 2019
// Date        : Mon Feb 10 14:55:12 2020
// Host        : fpga running 64-bit Ubuntu 18.04.4 LTS
// Command     : write_verilog top_vivado_syn.v
// Design      : top
// Purpose     : This is a Verilog netlist of the current design or from a specific cell of the design. The output is an
//               IEEE 1364-2001 compliant Verilog HDL file that contains netlist information obtained from the input
//               design files.
// Device      : xc7vx485tffg1157-1
// --------------------------------------------------------------------------------
`timescale 1 ps / 1 ps

(* STRUCTURAL_NETLIST = "yes" *)
module top
   (clk,
    rst,
    q);
  input clk;
  input rst;
  output [3:0]q;

  wire \<const1> ;
  wire clk;
  wire clk_IBUF;
  wire clk_IBUF_BUFG;
  wire [3:0]p_0_in;
  wire [3:0]q;
  wire [3:0]q_OBUF;
  wire rst;
  wire rst_IBUF;

  VCC VCC
       (.P(\<const1> ));
  BUFG clk_IBUF_BUFG_inst
       (.I(clk_IBUF),
        .O(clk_IBUF_BUFG));
  IBUF clk_IBUF_inst
       (.I(clk),
        .O(clk_IBUF));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT1 #(
    .INIT(2'h1)) 
    \q[0]_i_1 
       (.I0(q_OBUF[0]),
        .O(p_0_in[0]));
  (* SOFT_HLUTNM = "soft_lutpair1" *) 
  LUT2 #(
    .INIT(4'h6)) 
    \q[1]_i_1 
       (.I0(q_OBUF[0]),
        .I1(q_OBUF[1]),
        .O(p_0_in[1]));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT3 #(
    .INIT(8'h78)) 
    \q[2]_i_1 
       (.I0(q_OBUF[0]),
        .I1(q_OBUF[1]),
        .I2(q_OBUF[2]),
        .O(p_0_in[2]));
  (* SOFT_HLUTNM = "soft_lutpair0" *) 
  LUT4 #(
    .INIT(16'h7F80)) 
    \q[3]_i_1 
       (.I0(q_OBUF[1]),
        .I1(q_OBUF[0]),
        .I2(q_OBUF[2]),
        .I3(q_OBUF[3]),
        .O(p_0_in[3]));
  OBUF \q_OBUF[0]_inst 
       (.I(q_OBUF[0]),
        .O(q[0]));
  OBUF \q_OBUF[1]_inst 
       (.I(q_OBUF[1]),
        .O(q[1]));
  OBUF \q_OBUF[2]_inst 
       (.I(q_OBUF[2]),
        .O(q[2]));
  OBUF \q_OBUF[3]_inst 
       (.I(q_OBUF[3]),
        .O(q[3]));
  FDRE \q_reg[0] 
       (.C(clk_IBUF_BUFG),
        .CE(\<const1> ),
        .D(p_0_in[0]),
        .Q(q_OBUF[0]),
        .R(rst_IBUF));
  FDRE \q_reg[1] 
       (.C(clk_IBUF_BUFG),
        .CE(\<const1> ),
        .D(p_0_in[1]),
        .Q(q_OBUF[1]),
        .R(rst_IBUF));
  FDRE \q_reg[2] 
       (.C(clk_IBUF_BUFG),
        .CE(\<const1> ),
        .D(p_0_in[2]),
        .Q(q_OBUF[2]),
        .R(rst_IBUF));
  FDRE \q_reg[3] 
       (.C(clk_IBUF_BUFG),
        .CE(\<const1> ),
        .D(p_0_in[3]),
        .Q(q_OBUF[3]),
        .R(rst_IBUF));
  IBUF rst_IBUF_inst
       (.I(rst),
        .O(rst_IBUF));
endmodule
