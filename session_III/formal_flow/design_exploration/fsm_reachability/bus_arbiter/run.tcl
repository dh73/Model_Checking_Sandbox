clear -all
# Read in HDL files
analyze -clear
analyze -sv12 /home/diego/cinvestav/src/labs/session_III/formal_flow/design_exploration/fsm_reachability/fsm_sanity/bus_arbiter.sv
elaborate -top bus_arbiter
clock clk
reset -expression reset
