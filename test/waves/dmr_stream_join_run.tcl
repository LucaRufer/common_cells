# Compile
source compile.tcl

# Load
vsim dmr_stream_join_tb -voptargs="+acc"

# Waves
add wave -position end  sim:/dmr_stream_join_tb/clk
add wave -position end  sim:/dmr_stream_join_tb/rst_n
add wave -position end  sim:/dmr_stream_join_tb/sim_finished
add wave -position end  sim:/dmr_stream_join_tb/join_repeat
add wave -position end  sim:/dmr_stream_join_tb/join_error
add wave -position end  sim:/dmr_stream_join_tb/data_in
add wave -position end  sim:/dmr_stream_join_tb/valid_in
add wave -position end  sim:/dmr_stream_join_tb/ready_out
add wave -position end  sim:/dmr_stream_join_tb/data_out
add wave -position end  sim:/dmr_stream_join_tb/ready_in
add wave -position end  sim:/dmr_stream_join_tb/valid_out

add wave -position end  sim:/dmr_stream_join_tb/dut/data_q
add wave -position end  sim:/dmr_stream_join_tb/dut/state_q
add wave -position end  sim:/dmr_stream_join_tb/dut/latch_data
add wave -position end  sim:/dmr_stream_join_tb/dut/bypass

# Run
run -all