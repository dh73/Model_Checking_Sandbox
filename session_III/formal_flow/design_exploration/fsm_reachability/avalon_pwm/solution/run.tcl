clear -all;
# Read in HDL files
analyze -clear
analyze -sv12 /home/diego/cinvestav/src/labs/session_III/formal_flow/design_exploration/fsm_reachability/avalon_pwm/pwm_avalon_top.sv
analyze -sv12 /home/diego/cinvestav/src/labs/session_III/formal_flow/design_exploration/fsm_reachability/avalon_pwm/pwm_core.sv
elaborate -top pwm_avalon_top
# Setup environment after elaborate
# Setup global environment
# Setup global clocks and resets
clock clock
reset -expression !(resetn)
