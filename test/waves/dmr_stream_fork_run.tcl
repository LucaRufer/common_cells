# Compile
source compile.tcl

# Load
vsim dmr_stream_fork_tb -voptargs="+acc"

# Waves
add wave -position end  sim:/dmr_stream_fork_tb/clk
add wave -position end  sim:/dmr_stream_fork_tb/rst_n
add wave -position end  sim:/dmr_stream_fork_tb/sim_finished
add wave -position end  sim:/dmr_stream_fork_tb/fork_repeat
add wave -position end  sim:/dmr_stream_fork_tb/fork_error
add wave -position end  sim:/dmr_stream_fork_tb/data_in
add wave -position end  sim:/dmr_stream_fork_tb/valid_in
add wave -position end  sim:/dmr_stream_fork_tb/ready_out
add wave -position end  sim:/dmr_stream_fork_tb/data_out
add wave -position end  sim:/dmr_stream_fork_tb/ready_in
add wave -position end  sim:/dmr_stream_fork_tb/valid_out

add wave -position end  sim:/dmr_stream_fork_tb/dut/data_q
add wave -position end  sim:/dmr_stream_fork_tb/dut/state_q
add wave -position end  sim:/dmr_stream_fork_tb/dut/repeat_q
add wave -position end  sim:/dmr_stream_fork_tb/dut/latch_data
add wave -position end  sim:/dmr_stream_fork_tb/dut/bypass

# Run
run -all