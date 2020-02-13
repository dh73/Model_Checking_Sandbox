`default_nettype none
module pwm_core #(parameter R=10)
   (input  wire        i_clk, i_rst_n,
    input  wire [R:0]  i_duty,
    input  wire [31:0] i_dvsr,
    output logic       o_pwm);

   typedef struct packed {
      logic [R-1:0] d_reg, d_next;
      logic [R:0]   d_ext;
      logic         pwm_reg, pwm_next;
      logic [31:0]  q_reg, q_next;
      logic tick;
   } pwm_signals;
   pwm_signals ps_t;

   always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (~i_rst_n)
        begin
           ps_t.d_reg <= {R-1{1'b0}};
           ps_t.pwm_reg <= 1'b0;
           ps_t.q_reg <= 1'b0;
        end
      else
        begin
         ps_t.d_reg <= ps_t.d_next;
         ps_t.pwm_reg <= ps_t.pwm_next;
         ps_t.q_reg <= ps_t.q_next;
      end // else: !if(~i_rst_n)
   end // always_ff @ (posedge i_clk, negedge i_rst_n)

   // Preescale counter
   assign ps_t.q_next = (ps_t.q_reg == i_dvsr) ? 0 : ps_t.q_reg + 1'b1;
   assign ps_t.tick = ps_t.q_reg == 0;
   // Duty cycle counter
   assign ps_t.d_next = (ps_t.tick) ? ps_t.d_reg + 1'b1 : ps_t.d_reg;
   assign ps_t.d_ext = {1'b0, ps_t.d_reg};
   // comparison circuit
   assign ps_t.pwm_next = ps_t.d_ext < i_duty;
   assign o_pwm = ps_t.pwm_reg;
endmodule // pwm_core
