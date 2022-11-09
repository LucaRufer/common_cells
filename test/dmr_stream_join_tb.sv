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

module dmr_stream_join_tb;

  // Time Settings
  timeunit      1ns;
  timeprecision 1ps;

  // Number of outputs
  localparam int NUM_IN    = 2;
  localparam int DATA_BITS = 16;

  /**********************
   *  Clock and Timing  *
   **********************/

  // Timing parameters
  localparam ClockPeriod = 1ns;
  localparam TApply      = 0.2ns;
  localparam TTest       = 0.8ns;

  // clock and reset
  logic clk;
  logic rst_n;

  // Clock
  always #(ClockPeriod/2) clk = !clk;

  // Reset
  initial begin
    clk   = 1'b1;
    rst_n = 1'b0;
    repeat (5)
      #(ClockPeriod);
    rst_n = 1'b1;
  end

  /************************
   *  Stimuli generation  *
   ************************/

  // data type
  typedef logic [DATA_BITS-1:0] data_t;

  class stimuli_t;
    // Constants
    static const bit [NUM_IN-1:0] all_ones = {NUM_IN{1'b1}};

    // signals
    rand bit                  join_repeat;

    rand bit     [NUM_IN-1:0] valid;
    rand bit     [NUM_IN-1:0] data_error;
    rand data_t  [NUM_IN-1:0] data_bitflips;

    rand bit                  raise_ready;

    // constraints disabled during tests
    constraint no_repeat     { join_repeat == 1'b0;}
    constraint no_data_error { data_error  == '0;}
    constraint synchronous   { valid inside {'0, all_ones};}
    constraint always_ready  { raise_ready == 1'b1;}
    constraint always_valid  { valid == all_ones;}

    // dependancy constraints
    constraint correct_flip{ foreach(data_bitflips[i]) if(!data_error[i]) data_bitflips[i] == '0;
                             foreach(data_bitflips[i]) if( data_error[i]) data_bitflips[i] != '0;}

    // distribution constraints
    constraint error_dist  { data_error dist { '0 :/ 3, [('b1):all_ones] :/ 1}; }
    constraint valid_dist  { valid dist { '0                   :/ 1,
                                          [('b1):(all_ones-1)] :/ 1,
                                          all_ones             :/ 1};}
  endclass

  // stimuli queue
  stimuli_t stimuli_queue [$];

  // result type
  typedef struct packed {
    bit data_error;
    bit require_ready_out;
    bit require_valid_out;
  } expected_result_t;

  expected_result_t golden_queue [$];

  stimuli_t all_ready_stimuli;
  expected_result_t no_error_result;

  function automatic void generate_stimuli();
    // create default stimuli and results
    // default stimuli to retrieve buffered items
    all_ready_stimuli = new;
    all_ready_stimuli.join_repeat   = '0;
    all_ready_stimuli.valid         = '0;
    all_ready_stimuli.data_error    = '0;
    all_ready_stimuli.data_bitflips = '0;
    all_ready_stimuli.raise_ready   = 1'b1;
    // default result to retrieve buffered items
    no_error_result = '{
      data_error: '0,
      require_ready_out: '0,
      require_valid_out: '0
    };

    // 1st phase: check maximum throughput with no errors & no repeats
    for (int i = 0; i < 10; i++) begin
      // new stimuli
      automatic stimuli_t stimuli = new;
      // Randomize
      if (stimuli.randomize()) begin
        stimuli_queue.push_back(stimuli);
        golden_queue.push_back('{data_error: 1'b0,
                                 require_ready_out: 1'b1,
                                 require_valid_out: 1'b1});
      end else begin
        $error("Could not randomize.");
      end
    end

    // clear remaining items
    repeat (5) begin
      stimuli_queue.push_back(all_ready_stimuli);
      golden_queue.push_back(no_error_result);
    end

    // 2nd phase: do random testing, no errors, no repeats
    for (int i = 0; i < 50; i++) begin
      // new stimuli
      automatic stimuli_t stimuli = new;
      // disable unused constraints
      stimuli.always_ready.constraint_mode(0);
      stimuli.always_valid.constraint_mode(0);
      // Randomize
      if (stimuli.randomize()) begin
        stimuli_queue.push_back(stimuli);
        golden_queue.push_back('{data_error: '0,
                                 require_ready_out: '0,
                                 require_valid_out: &stimuli.valid});
      end else begin
        $error("Could not randomize.");
      end
    end

    // clear remaining items
    repeat (5) begin
      stimuli_queue.push_back(all_ready_stimuli);
      golden_queue.push_back(no_error_result);
    end

    // 3rd phase: do completely random testing
    for (int i = 0; i < 200; i++) begin
      // new stimuli
      automatic stimuli_t stimuli = new;
      // disable unused constraints
      stimuli.no_repeat.constraint_mode(0);
      stimuli.no_data_error.constraint_mode(0);
      stimuli.synchronous.constraint_mode(0);
      stimuli.always_ready.constraint_mode(0);
      stimuli.always_valid.constraint_mode(0);
      // Randomize
      if (stimuli.randomize()) begin
        stimuli_queue.push_back(stimuli);
        golden_queue.push_back('{data_error: |stimuli.data_error,
                                 require_ready_out: '0,
                                 require_valid_out: &stimuli.valid &
                                                    !(|stimuli.data_error) &
                                                    !stimuli.join_repeat});
      end else begin
        $error("Could not randomize.");
      end
    end

    // clear remaining items
    repeat (5) begin
      stimuli_queue.push_back(all_ready_stimuli);
      golden_queue.push_back(no_error_result);
    end
  endfunction : generate_stimuli

  /*******************
   *  apply stimuli  *
   *******************/

  // control signals
  logic join_repeat, join_error;

  // Data input side
  data_t [NUM_IN-1:0] data_in;
  logic  [NUM_IN-1:0] valid_in, ready_out;

  // Data output side
  data_t data_out;
  logic  ready_in, valid_out;

  // other
  data_t current_data = 0;

  task automatic apply_stimuli();
    automatic stimuli_t stimuli;
    logic handshake_in_complete, handshake_out_complete;
    // get the next stimuli
    wait (stimuli_queue.size() != '0);
    stimuli = stimuli_queue.pop_front();
    @(posedge clk);
    // check for completed handshakes
    handshake_in_complete = '0;
    handshake_out_complete = '0;
    if(&valid_in & &ready_out & !join_repeat & !join_error) begin
      handshake_in_complete = 1'b1;
      current_data += 1;
    end
    if(valid_out & ready_in) begin
      handshake_out_complete = 1'b1;
    end
    // Wait for apply time
    #(TApply);
    // revoke signals for completed handshakes
    if(handshake_in_complete)  valid_in = '0;
    if(handshake_out_complete) ready_in = '0;
    // apply stimuli
    join_repeat = stimuli.join_repeat;
    valid_in = stimuli.valid;
    ready_in |= stimuli.raise_ready;
    for(int i = 0; i < NUM_IN; i++) begin
      data_in[i] = current_data ^ stimuli.data_bitflips[i];
    end
  endtask : apply_stimuli

  /***********************
   *  Device Under Test  *
   ***********************/

  dmr_stream_join #(
    .T       ( data_t  ),
    .NUM_IN  ( NUM_IN  )
  ) i_dut (
    .clk_i    ( clk          ),
    .rst_ni   ( rst_n        ),
    .repeat_i ( join_repeat  ),
    .error_o  ( join_error   ),
    .valid_i  ( valid_in     ),
    .ready_o  ( ready_out    ),
    .data_i   ( data_in      ),
    .valid_o  ( valid_out    ),
    .ready_i  ( ready_in     ),
    .data_o   ( data_out     )
  );

  /***********************
   *  Output collection  *
   ***********************/

  typedef struct packed {
    bit error;
    bit ready_out;
    bit valid_out;
    bit received_data;
    data_t data;
  } result_t;

  result_t result_queue [$];

  task automatic collect_result;
    result_t result;
    // wait for test time
    @(posedge clk)
    #(TTest);
    // collect the results
    result.error = join_error;
    result.ready_out = &ready_out;
    result.valid_out = valid_out;
    result.received_data = (valid_out & ready_in);
    result.data = data_out;
    result_queue.push_back(result);
  endtask : collect_result

  /*************
   *  Checker  *
   *************/

  data_t next_aquired_data = '0;
  time last_consumed = '0;

  task automatic check_result;
    automatic result_t result;
    automatic expected_result_t golden;

    do begin
      wait(result_queue.size() != 0);

      // extract the result
      result = result_queue.pop_front();
      golden = golden_queue.pop_front();

      // compare the results
      if(golden.data_error & !result.error)
        $error("[Data Error] Error injected in data not detected.");
      if(golden.require_valid_out & !result.valid_out)
        $error("[Vailid Out Error] Expected valid out to be raised.");
      if(result.received_data) begin
        if(result.data < next_aquired_data) begin
          $error("[Data Error] Item %h was aquired again. Waiting for %h. Last item consumed at %d.", result.data, next_aquired_data, last_consumed);
        end else if (result.data > next_aquired_data) begin
          $error("[Data Error] Item %h was aquired again. Waiting for %h. Last item consumed at %d.", result.data, next_aquired_data, last_consumed);
          next_aquired_data = result.data + 'd1;
          last_consumed = $time;
        end else begin
          next_aquired_data += 'd1;
          last_consumed = $time;
        end
      end
    end while (golden_queue.size() != 0);
    if(current_data != next_aquired_data)
      $error("[Data Error] Sent %d items, received %d items.", current_data, next_aquired_data);
  endtask : check_result

  // make sure handshake signals are not revoked
  assert property (@(posedge clk) disable iff (~rst_n) ( valid_out & ~ready_in ) |=> valid_out) else begin
    $error("[Input Handshake Violation] valid_out revoked before valid handshake");
  end
  assert property (@(posedge clk) disable iff (~rst_n) (~valid_out &  ready_in ) |=> ready_in) else begin
    $error("[Input Handshake Violation] ready_in revoked before valid handshake");
  end

  for (genvar i = 0; i < NUM_IN; i++) begin
    //assert property (@(posedge clk) disable iff (~rst_n) ( valid_in[i] & ~ready_out[i] ) |=> valid_in[i]) else begin
    //  $error("[Output Handshake Violation] valid_in[%d] revoked before valid handshake", i);
    //end
    assert property (@(posedge clk) disable iff (~rst_n) (~valid_in[i] &  ready_out[i] ) |=> ready_out[i]) else begin
      $error("[Output Handshake Violation] ready_out[%d] revoked before valid handshake", i);
    end
  end

  task run_apply();
    forever begin
      apply_stimuli();
    end
  endtask : run_apply

  task run_collect();
    forever begin
      collect_result();
    end
  endtask : run_collect

  initial begin : tb
    // Initialize variables
    join_repeat = '0;
    data_in = '0;
    valid_in = '0;
    ready_in = '0;

    @(posedge rst_n)
    repeat(10) @(posedge clk);

    fork
      run_apply();
      run_collect();
      fork
        generate_stimuli();
        check_result();
      join
    join_any

    $finish(0);
  end : tb

endmodule
