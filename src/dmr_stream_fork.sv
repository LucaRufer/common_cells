// Copyright 2022 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Luca Rufer <lrufer@student.ethz.ch>


/// Fork a stream of data to multiple desinations. All destinations must reveice
/// the same output signals, but may provide different input signals.
/// As long as the external repeat signal is active, or the ready signals from
/// the destinations don't agree, the output data will be repeated.
/// An error signal will be generated in the ready_i signals don't agree
module dmr_stream_fork #(
  parameter type T           = logic,
  parameter int  NUM_OUT     = 2
)(
  input  logic clk_i,
  input  logic rst_ni,
  input  logic repeat_i,
  output logic error_o,
  // stream source
  input  logic valid_i,
  output logic ready_o,
  input  T     data_i,
  // stream destination
  output logic [NUM_OUT-1:0] valid_o,
  input  logic [NUM_OUT-1:0] ready_i,
  output T     [NUM_OUT-1:0] data_o
);

  T data_d, data_q;
  logic repeat_d, repeat_q;
  logic latch_data, bypass;

  enum logic {
    Waiting,
    Latched
  } state_d, state_q;

  assign data_d = latch_data ? data_i : data_q;
  assign repeat_d = repeat_i;
  assign error_o = (|ready_i) & (~&ready_i);
  assign ready_o = latch_data;
  for (genvar i = 0; i < NUM_OUT; i++) begin
    assign data_o[i] = bypass ? data_i : data_q;
  end

  always_comb begin
    state_d = state_q;
    latch_data = 1'b0;
    bypass = 1'b0;
    valid_o = '0;

    // proceed to next state if no repeat required
    unique case (state_q)
      Waiting: begin
        // check if new data is available
        if(valid_i) begin
          // no not change the state or the output if we have to repeat the cycle
          if(!repeat_q || !repeat_i) begin
            // latch the new data
            latch_data = 1'b1;
          end
          // check if we cannot forward the data and only latch it
          if((!(&ready_i) && !repeat_i) || (repeat_q ^ repeat_i)) begin
            state_d = Latched;
          end
          // if we are not repeating in this cycle, we can direcly output the data
          valid_o = {NUM_OUT{1'b1}};
          bypass = 1'b1;
        end
      end
      Latched: begin
        // check if output handshake is ready to release data
        if(&ready_i && !repeat_i) begin
          // check if input handshake has new data ready
          if(valid_i) begin
            // old data way consumed, new data can be directly latched in
            latch_data = 1'b1;
          end else begin
            // output data was consumed, no input data ready -> wait for new data
            state_d = Waiting;
          end
        end
        // In latched state, data is always valid
        valid_o = {NUM_OUT{1'b1}};
      end
      default: begin
      end
    endcase
  end

  // state update
  always_ff @(posedge (clk_i) or negedge (rst_ni)) begin
    if (!rst_ni) begin
      data_q <= '0;
      state_q <= Waiting;
      repeat_q <= 1'b0;
    end else begin
      data_q <= data_d;
      state_q <= state_d;
      repeat_q <= repeat_d;
    end
  end

endmodule
