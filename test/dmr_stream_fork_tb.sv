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

module dmr_stream_fork_tb;

  // Time Settings
  timeunit      1ns;
  timeprecision 1ps;

  // Timing parameters
  localparam ClockPeriod = 1ns;
  localparam TA          = 0.2ns;
  localparam TT          = 0.8ns;
  localparam EPSILON     = 0.05ns;

  // Number of outputs
  localparam int NUM_OUT = 2;

  // data type
  typedef logic [15:0] data_t;

  // control signals
  logic fork_repeat, fork_error;

  // Data input side
  data_t data_in;
  logic  valid_in, ready_out;

  // Data output side
  data_t [NUM_OUT-1:0] data_out;
  logic  [NUM_OUT-1:0] ready_in, valid_out;

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

  // dut
  dmr_stream_fork #(
    .T       ( data_t  ),
    .NUM_OUT ( NUM_OUT )
  ) i_dut (
    .clk_i    ( clk          ),
    .rst_ni   ( rst_n        ),
    .repeat_i ( fork_repeat ),
    .error_o  ( fork_error   ),
    .valid_i  ( valid_in     ),
    .ready_o  ( ready_out    ),
    .data_i   ( data_in      ),
    .valid_o  ( valid_out    ),
    .ready_i  ( ready_in     ),
    .data_o   ( data_out     )
  );

  // make sure handshake signals are not revoked
  assert property (@(posedge clk) disable iff (~rst_n) ( ready_out & ~valid_in ) |=> ready_out) else begin
    $error("[Input Handshake Violation] ready_out revoked before valid handshake");
  end
  assert property (@(posedge clk) disable iff (~rst_n) (~ready_out &  valid_in ) |=> valid_in) else begin
    $error("[Input Handshake Violation] valid_in revoked before valid handshake");
  end

  for (genvar i = 0; i < NUM_OUT; i++) begin
    //assert property (@(posedge clk) disable iff (~rst_n) ( ready_in[i] & ~valid_out[i] ) |=> ready_in[i]) else begin
    //  $error("[Output Handshake Violation] ready_in[%d] revoked before valid handshake", i);
    //end
    assert property (@(posedge clk) disable iff (~rst_n) (~ready_in[i] &  valid_out[i] ) |=> valid_out[i]) else begin
      $error("[Output Handshake Violation] valid_out[%d] revoked before valid handshake", i);
    end
  end

  // make sure output signals are consitent over all outputs
  for (genvar i = 0; i < NUM_OUT; i++) begin
    assert property(@(posedge clk) disable iff (~rst_n) (data_out[i] == data_out[0])) else begin
      $error("[Output Data Mismatch] [OUT%d] reads %d, [OUT0] reads %d", i, data_out[i], data_out[0]);
    end
    assert property(@(posedge clk) disable iff (~rst_n) (valid_out[i] == valid_out[0])) else begin
      $error("[Output Valid Mismatch] [OUT%d] reads %b, [OUT0] reads %b", i, valid_out[i], valid_out[0]);
    end
  end

  // make sure the repeat functions correctly
  property correct_data_repeat;
    data_t [NUM_OUT-1:0] prev_data_out;
    @(posedge clk) disable iff (~rst_n) (fork_repeat & (&valid_out), prev_data_out=data_out) |=> (prev_data_out==data_out);
  endproperty
  property correct_valid_repeat;
    @(posedge clk) disable iff (~rst_n) (fork_repeat & (&valid_out)) |=> (&valid_out);
  endproperty

  assert property (correct_data_repeat) else begin
    $error("[Incorrect Repeat] Data was changed");
  end

  assert property (correct_valid_repeat) else begin
    $error("[Incorrect Repeat] Valid was revoked");
  end

  class Provider;

    data_t next_item;

    function new();
      next_item = 'b0;
    endfunction

    function data_t next();
      next = this.next_item;
      this.next_item = this.next_item + 'd1;
    endfunction
  endclass

  class Consumer;

    data_t num_consumed;
    int    last_consumed = 0;

    function new();
      num_consumed = 'd0;
    endfunction

    function void consume(data_t item);
      if (item < num_consumed) begin
        $error("[Consumer] consumed %h again. Last Item consumed at %d", item, last_consumed);
      end else if (item > num_consumed) begin
        $error("[Consumer] Skipped Data! Expeced item %h, consumed %h. Last Item consumed at %d", num_consumed, item, last_consumed);
        num_consumed = item + 'd1;
      end else begin
        num_consumed += 'd1;
      end
      last_consumed = $time;
    endfunction
  endclass

  Provider provider;
  Consumer consumer [NUM_OUT-1:0];

  logic sim_finished;
  logic new_valid_in;
  logic new_repeat;
  logic [NUM_OUT-1:0] new_ready_in;

  initial begin: controller_block
    // controller controlls: fork_repeat, data_in, valid_in, ready_in[NUM_OUT]
    fork_repeat = 1'b0;
    data_in = 'b0;
    valid_in = 1'b0;
    ready_in = {NUM_OUT{1'b0}};

    // controller checks: fork_error, ready_out, valid_out[NUM_OUT]

    // Initialize testbench controller
    sim_finished = 1'b0;
    provider = new();
    wait (rst_n);

    // check maximum throughput with no errors & no repeats
    fork_repeat = 1'b0;
    for(int i = 0; i < 10; i++) begin
      @(posedge clk);
      // Generate inputs
      #(TA);
      ready_in = {NUM_OUT{1'b1}};
      valid_in = 1'b1;
      data_in = provider.next();
      // Check outputs
      #(TT-TA);
      assert(!fork_error);
      assert(ready_out);
      assert(valid_out == {NUM_OUT{1'b1}});
    end

    // consume remaining data
    ready_in = {NUM_OUT{1'b1}};
    fork_repeat = 1'b0;
    repeat (5) begin
      @(posedge clk);
      #(TA);
      ready_in = {NUM_OUT{1'b1}};
    end

    // do random testing, no errors, no repeats
    fork_repeat = 1'b0;
    for(int i = 0; i < 50; i++) begin
      @(posedge clk);
      // Generate inputs
      new_valid_in = $urandom();
      new_ready_in = $urandom();
      new_ready_in = {NUM_OUT{new_ready_in[0]}};
      #(TA);
      // apply inputs
      if(new_valid_in & !valid_in) data_in = provider.next();
      valid_in |= new_valid_in;
      ready_in |= new_ready_in;
      // Check outputs
      #(TT-TA);
      assert(!fork_error);
    end

    // consume remaining data
    fork_repeat = 1'b0;
    repeat (5) begin
      @(posedge clk);
      #(TA);
      ready_in = {NUM_OUT{1'b1}};
    end

    // do random testing
    for(int i = 0; i < 200; i++) begin
      @(posedge clk);
      // Generate inputs
      new_valid_in = $urandom();
      new_repeat   = $urandom();
      new_ready_in = $urandom();
      #(TA);
      // apply inputs
      if(new_valid_in & ~valid_in) data_in = provider.next();
      valid_in |= new_valid_in;
      fork_repeat = new_repeat;
      ready_in = new_ready_in;
      // Check outputs
      #(TT-TA);
      assert(~fork_error == (~|ready_in) | (&ready_in));
    end

    // consume remaining data
    fork_repeat = 1'b0;
    repeat (5) begin
      @(posedge clk);
      #(TA);
      ready_in = {NUM_OUT{1'b1}};
    end

    // End simulation
    sim_finished = 1'b1;
  end

  logic [NUM_OUT-1:0] valid_output_handshake;
  logic               valid_input_handshake;

  initial begin: handshake_reset_block
    // wait until the end of the reset
    wait (rst_n);

    // loop forever
    while (1) begin
      @(posedge clk);
      // check which handshake signals are valid
      for(int i = 0; i < NUM_OUT; i++) begin
        valid_output_handshake[i] = valid_out[i] & ready_in[i] & !fork_repeat & !fork_error;
      end
      valid_input_handshake = valid_in & ready_out;

      #(EPSILON);
      // revoke handshake signals if handshakes were valid
      for(int i = 0; i < NUM_OUT; i++) begin
        if(valid_output_handshake[i]) begin
          ready_in[i] = 1'b0;
        end
      end
      if(valid_input_handshake) begin
        valid_in = 1'b0;
        // set data to invalid to detect errors when invalid data is latched
        data_in = 'bx;
      end
    end
  end

  initial begin: acquire_block
    for(int i = 0; i < NUM_OUT; i++) begin
      consumer[i] = new();
    end

    wait (rst_n);
    while (1) begin
      @(posedge clk);
      // if handshake valid, no repeat and no error, consume the item
      for(int i = 0; i < NUM_OUT; i++) begin
        if(valid_out[i] & ready_in[i] & !fork_repeat & !fork_error) begin
          consumer[i].consume(data_out[i]);
        end
      end
      // At the end of the simulation, check if all items were consumed
      if(sim_finished) begin
        for(int i = 0; i < NUM_OUT; i++) begin
          assert(consumer[i].num_consumed == provider.next_item) else begin
            $error("Consumer %d consumed %d items, but %d were provided.", i, consumer[i].num_consumed, provider.next_item);
          end
        end
        $finish(0);
      end
    end
  end

endmodule
