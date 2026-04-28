// tb_pipeline.sv — Self-checking testbench for pipeline.sv
//
// Tests:
//   1. Known value propagates through STAGES cycles and appears at output
//   2. Reset clears all pipeline stages mid-flight

`default_nettype none
`timescale 1ns/1ps

module tb_pipeline;

    // Parameters under test
    localparam int STAGES = 4;
    localparam int WIDTH  = 8;

    // DUT ports
    logic            clk;
    logic            rst_n;
    logic [WIDTH-1:0] data_in;
    logic [WIDTH-1:0] data_out;

    // Instantiate DUT
    pipeline #(
        .STAGES(STAGES),
        .WIDTH (WIDTH)
    ) dut (
        .clk     (clk),
        .rst_n   (rst_n),
        .data_in (data_in),
        .data_out(data_out)
    );

    // Clock generation: 10 ns period
    initial clk = 1'b0;
    always #5 clk = ~clk;

    // Test stimulus
    logic test_failed;

    initial begin
        test_failed = 1'b0;
        rst_n       = 1'b0;
        data_in     = 8'h00;

        // Assert reset for 3 cycles
        repeat (3) @(posedge clk);
        #1;
        rst_n = 1'b1;

        // ----------------------------------------------------------------
        // Test 1: inject a known value and verify it appears STAGES cycles later
        // ----------------------------------------------------------------

        // Wait one cycle after reset release
        @(posedge clk); #1;

        // Drive known value for one cycle
        data_in = 8'hA5;
        @(posedge clk); #1;

        // Drive zeros so we can track the A5 bubble
        data_in = 8'h00;

        // Wait STAGES-1 more cycles; A5 should reach the output after STAGES total
        repeat (STAGES - 1) @(posedge clk); #1;

        // data_out should hold 8'hA5
        if (data_out !== 8'hA5) begin
            $display("FAIL: Test1 propagation: expected 0xA5 got 0x%02X after %0d stages", data_out, STAGES); $finish;
        end

        // ----------------------------------------------------------------
        // Test 2: reset clears pipeline mid-flight
        // ----------------------------------------------------------------

        // Fill pipeline with non-zero values
        data_in = 8'hFF;
        repeat (STAGES) @(posedge clk); #1;

        // Assert reset while pipeline is full
        rst_n = 1'b0;
        @(posedge clk); #1;

        // Output should be cleared to 0 after reset asserts
        if (data_out !== 8'h00) begin
            $display("FAIL: Test2 reset: expected 0x00 got 0x%02X after reset", data_out); $finish;
        end

        // Release reset; verify pipeline stays cleared with no input
        rst_n   = 1'b1;
        data_in = 8'h00;
        @(posedge clk); #1;

        if (data_out !== 8'h00) begin
            $display("FAIL: Test2 post-reset: expected 0x00 got 0x%02X", data_out); $finish;
        end

        // ----------------------------------------------------------------
        // All checks passed
        // ----------------------------------------------------------------
        $display("PASS"); $finish;
    end

    // Safety timeout
    initial begin
        #10000;
        $display("FAIL: simulation timeout"); $finish;
    end

endmodule
