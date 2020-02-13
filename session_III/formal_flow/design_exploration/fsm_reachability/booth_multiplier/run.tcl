clear -all
# Read in HDL files
analyze -clear
analyze -sv12 /home/diego/cinvestav/src/labs/session_III/formal_flow/design_exploration/fsm_reachability/asmd/booth_multiplier/booth_mult.sv
elaborate -top booth_mult
clock clk
reset -expression !(reset_n)
