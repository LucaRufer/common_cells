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


/// Join a stream of data to multiple sources. All sources may provide different
/// input signals, but must reveice the same input signals signals.
/// As long as the external repeat signal is active, or the data or valid
/// signals from the source don't agree, the outgoing data will not be marked as
/// valid.
/// An error signal is generated if the valid_i signals or data signals
/// don't agree
module dmr_stream_join #(
  parameter type T           = logic,
  parameter int  NUM_IN      = 2
)(
  input  logic clk_i   ,
  input  logic rst_ni  ,
  input  logic repeat_i,
  output logic error_o ,
  // stream source
  input  logic [NUM_IN-1:0] valid_i,
  output logic [NUM_IN-1:0] ready_o,
  input  T     [NUM_IN-1:0] data_i ,
  // stream desitination
  output logic valid_o,
  input  logic ready_i,
  output T     data_o
);

  enum logic {
    Waiting,
    Latched
  } state_d, state_q;

  T data_d, data_q;
  logic latch_data, bypass;

  assign data_o = bypass ? data_i[0] : data_q;
  assign data_d = latch_data ? data_i : data_q;
  assign ready_o = {NUM_IN{latch_data}};

  always_comb begin
    error_o = 1'b0;

    // output comparator logic
    for(int i = 1; i < NUM_IN; i++) begin
      if(data_i[i] != data_i[0] || valid_i[i] != valid_i[0]) begin
        error_o = 1'b1;
      end
    end

    valid_o = 1'b0;
    latch_data = 1'b0;
    bypass = 1'b0;
    state_d = state_q;

    // state control
    unique case (state_q)
      Waiting: begin
        // check if new data is valid and without errors
        if(&valid_i & !error_o & !repeat_i) begin
          // latch the new data
          latch_data = 1'b1;
          // send the data directly to the output
          bypass = 1'b1;
          // indicate that the ougoing data is valid
          valid_o = 1'b1;
          // check if the outgoing interface is ready
          if(!ready_i) begin
            state_d = Latched;
          end
        end
      end
      Latched: begin
        // In latched state, data is always valid
        valid_o = 1'b1;
        // check if outgoing handshake is accepted
        if(ready_i) begin
          // check if incomming data is valid
          if(&valid_i && !error_o &!repeat_i) begin
            // latch new incomming data for the next transaction
            latch_data = 1'b1;
          end else begin
            // invalid data is not valid, go to waiting state
            state_d = Waiting;
          end
        end
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
    end else begin
      data_q <= data_d;
      state_q <= state_d;
    end
  end

endmodule
