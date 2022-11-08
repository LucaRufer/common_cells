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

`define RANDOM_BIT_VECTOR_NORMALLY_ZERO(N_BITS, P_ZERO)               \
                          (($urandom() <= (P_ZERO * 32'hFFFFFFFF)) ?  \
                           {(N_BITS){1'b0}} :                         \
                           ($urandom() & ((1<<N_BITS) - 1)))          \

module dmr_stream_join_tb;

  // Time Settings
  timeunit      1ns;
  timeprecision 1ps;

  // Timing parameters
  localparam ClockPeriod = 1ns;
  localparam TA          = 0.2ns;
  localparam TT          = 0.8ns;
  localparam EPSILON     = 0.05ns;

  // Number of outputs
  localparam int NUM_IN    = 2;
  localparam int DATA_BITS = 16;

  // data type
  typedef logic [DATA_BITS-1:0] data_t;

  // control signals
  logic join_repeat, join_error;

  // Data input side
  data_t [NUM_IN-1:0] data_in;
  logic  [NUM_IN-1:0] valid_in, ready_out;

  // Data output side
  data_t data_out;
  logic  ready_in, valid_out;

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
  dmr_stream_join #(
    .T       ( data_t  ),
    .NUM_IN  ( NUM_IN )
  ) i_dut (
    .clk_i    ( clk          ),
    .rst_ni   ( rst_n        ),
    .repeat_i ( join_repeat ),
    .error_o  ( join_error   ),
    .valid_i  ( valid_in     ),
    .ready_o  ( ready_out    ),
    .data_i   ( data_in      ),
    .valid_o  ( valid_out    ),
    .ready_i  ( ready_in     ),
    .data_o   ( data_out     )
  );

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
  Consumer consumer;

  logic sim_finished;
  logic new_ready_in;
  logic new_repeat;
  logic [NUM_IN-1:0] new_valid_in, new_data_bitflips;
  data_t next_data_item;

  initial begin: controller_block
    // controller controlls: join_repeat, data_in, valid_in, ready_in
    join_repeat = 1'b0;
    data_in = {DATA_BITS*NUM_IN{1'b0}};
    valid_in = {NUM_IN{1'b0}};
    ready_in = 1'b0;
    next_data_item = 'b0;

    // controller checks: join_error, ready_out, valid_out

    // Initialize testbench controller
    sim_finished = 1'b0;
    provider = new();
    wait (rst_n);

    // check maximum throughput with no errors & no repeats
    join_repeat = 1'b0;
    for(int i = 0; i < 10; i++) begin
      @(posedge clk);
      // Generate inputs
      #(TA);
      valid_in = {NUM_IN{1'b1}};
      next_data_item = provider.next();
      data_in = {NUM_IN{next_data_item}};
      ready_in = 1'b1;
      // Check outputs
      #(TT-TA);
      assert(!join_error);
      assert(ready_out == {NUM_IN{1'b1}});
      assert(valid_out == 1'b1);
    end

    // consume remaining data
    ready_in = 1'b1;
    repeat (5) begin
      @(posedge clk);
      #(TA);
      ready_in = 1'b1;
    end

    // do random testing, no errors, no repeats
    join_repeat = 1'b0;
    for(int i = 0; i < 50; i++) begin
      @(posedge clk);
      // Generate inputs
      new_valid_in = $urandom();
      new_valid_in = {NUM_IN{new_valid_in[0]}};
      new_ready_in = $urandom();
      #(TA);
      // apply inputs
      if(new_valid_in[0] & !valid_in[0]) next_data_item = provider.next();
      data_in = {NUM_IN{next_data_item}};
      valid_in |= new_valid_in;
      ready_in |= new_ready_in;
      // Check outputs
      #(TT-TA);
      assert(!join_error);
      if(&valid_in) assert(valid_out);
    end

    // consume remaining data
    ready_in = 1'b1;
    join_repeat = 1'b0;
    repeat (5) begin
      @(posedge clk);
      #(TA);
      ready_in = 1'b1;
    end

    // do random testing
    next_data_item = provider.next();
    for(int i = 0; i < 200; i++) begin
      @(posedge clk);
      // Generate inputs
      new_valid_in = ~(`RANDOM_BIT_VECTOR_NORMALLY_ZERO(NUM_IN, 0.5));
      new_data_bitflips = (`RANDOM_BIT_VECTOR_NORMALLY_ZERO(NUM_IN, 0.5));
      new_repeat   = $urandom();
      new_ready_in = $urandom();
      if(&valid_in & &ready_out & !join_repeat & !join_error) begin
        next_data_item = provider.next();
      end
      #(TA);
      // apply inputs
      valid_in = new_valid_in;
      for(int i = 0; i < NUM_IN; i++) begin
        if(!valid_in[i]) begin
          data_in[i] = {DATA_BITS{1'bx}};
        end else begin
          if(new_data_bitflips[i]) begin
            data_in[i] = next_data_item ^ $urandom();
            if(data_in[i] == next_data_item) new_data_bitflips[i] = 1'b0;
          end else begin
            data_in[i] = next_data_item;
          end
        end
      end
      join_repeat = new_repeat;
      ready_in |= new_ready_in;
      // Check outputs
      #(TT-TA);
      assert(join_error == !((~|valid_in | (&valid_in & ~|new_data_bitflips))));
      if(&valid_in & !join_repeat & !join_error) assert(valid_out);
    end

    // consume remaining data
    ready_in = 1'b1;
    join_repeat = 1'b0;
    data_in = {NUM_IN{next_data_item}};
    valid_in = {NUM_IN{1'b1}};
    repeat (5) begin
      @(posedge clk);
      #(TA);
      ready_in = 1'b1;
    end

    // End simulation
    sim_finished = 1'b1;
  end

  logic [NUM_IN-1:0] valid_input_handshake;
  logic              valid_output_handshake;

  initial begin: handshake_reset_block
    // wait until the end of the reset
    wait (rst_n);

    // loop forever
    while (1) begin
      @(posedge clk);
      // check which handshake signals are valid
      for(int i = 0; i < NUM_IN; i++) begin
        valid_input_handshake[i] = valid_in[i] & ready_out[i] & !join_repeat & !join_error;
      end
      valid_output_handshake = valid_out & ready_in;

      #(EPSILON);
      // revoke handshake signals if handshakes were valid
      for(int i = 0; i < NUM_IN; i++) begin
        if(valid_input_handshake[i]) begin
          valid_in[i] = 1'b0;
          // set data to invalid to detect errors when invalid data is latched
          data_in[i] = {DATA_BITS{1'bx}};
        end
      end
      if(valid_output_handshake) begin
        ready_in = 1'b0;
      end
    end
  end

  initial begin: acquire_block
    consumer = new();

    wait (rst_n);
    while (1) begin
      @(posedge clk);
      // if handshake valid, no repeat and no error, consume the item
      if(valid_out & ready_in) begin
        consumer.consume(data_out);
      end
      // At the end of the simulation, check if all items were consumed
      if(sim_finished) begin
        assert(consumer.num_consumed == provider.next_item) else begin
          $error("Consumer consumed %d items, but %d were provided.", consumer.num_consumed, provider.next_item);
        end
        $finish(0);
      end
    end
  end

endmodule
