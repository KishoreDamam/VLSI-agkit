// tb_sync_2ff.sv — Self-checking testbench for sync_2ff
//
// Tests:
//   1. d=1 propagates to q within STAGES+2 destination clock cycles
//   2. Reset forces q=0 even when d=1
//
// Compile and run:
//   iverilog -g2012 -Wall sync_2ff.sv tb_sync_2ff.sv && vvp a.out

`timescale 1ns/1ps
`default_nettype none

module tb_sync_2ff;

    // Parameters matching DUT instantiation
    localparam int WIDTH  = 1;
    localparam int STAGES = 2;
    localparam int MAX_WAIT = STAGES + 2;  // cycles before we call it a failure

    // Destination clock: 10 ns period (100 MHz)
    localparam real DST_PERIOD = 10.0;

    // DUT ports
    logic             clk_dst;
    logic             rst_n;
    logic [WIDTH-1:0] d;
    logic [WIDTH-1:0] q;

    // Instantiate DUT
    sync_2ff #(
        .WIDTH (WIDTH),
        .STAGES(STAGES)
    ) dut (
        .clk_dst(clk_dst),
        .rst_n  (rst_n),
        .d      (d),
        .q      (q)
    );

    // Generate destination clock
    initial clk_dst = 1'b0;
    always #(DST_PERIOD/2) clk_dst = ~clk_dst;

    // ──────────────────────────────────────────────────────────────────────
    // Test logic
    // ──────────────────────────────────────────────────────────────────────
    integer cycle_count;
    integer failed;

    initial begin
        failed = 0;
        d      = 1'b0;
        rst_n  = 1'b0;

        // Apply reset for 3 destination clock cycles
        @(negedge clk_dst); @(negedge clk_dst); @(negedge clk_dst);
        rst_n = 1'b1;

        // ── Test 1: d=1 propagates to q within MAX_WAIT cycles ────────────
        // Drive d from "source domain" — use a #delay not a separate clock,
        // simulating an asynchronous data change between dst clock edges.
        #(DST_PERIOD * 0.3);  // change d 30% into a dst cycle (async arrival)
        d = 1'b1;

        cycle_count = 0;
        @(posedge clk_dst); #1;  // sample just after rising edge
        while (q !== 1'b1 && cycle_count < MAX_WAIT) begin
            @(posedge clk_dst); #1;
            cycle_count = cycle_count + 1;
        end

        if (q !== 1'b1) begin
            $display("FAIL: Test 1 — d=1 did not propagate to q within %0d cycles (cycle_count=%0d)",
                     MAX_WAIT, cycle_count);
            failed = failed + 1;
        end

        // ── Test 2: Reset forces q=0 even when d=1 ───────────────────────
        // d is still 1 from previous test; assert reset and check q goes 0
        @(negedge clk_dst);
        rst_n = 1'b0;           // async assert
        #1;                      // 1 ns after negedge

        if (q !== 1'b0) begin
            $display("FAIL: Test 2 — q did not go 0 immediately on async reset (q=%b)", q);
            failed = failed + 1;
        end

        // Hold reset for 2 more cycles
        @(negedge clk_dst); @(negedge clk_dst);

        // Release reset while d=1; q must remain 0 immediately after release
        rst_n = 1'b1;
        #1;  // 1 ns after release — pipe[0] is d=1 but not yet clocked through

        // After STAGES cycles, q should become 1 again (reset released, d=1)
        repeat (STAGES + 1) @(posedge clk_dst);
        #1;
        if (q !== 1'b1) begin
            $display("FAIL: Test 2b — q did not recover to 1 after reset release (q=%b)", q);
            failed = failed + 1;
        end

        // ── Final report ──────────────────────────────────────────────────
        if (failed == 0)
            $display("PASS");
        else
            $display("FAIL: %0d test(s) failed", failed);

        $finish;
    end

    // Timeout watchdog — bail after 200 cycles to avoid infinite simulation
    initial begin
        #(DST_PERIOD * 200);
        $display("FAIL: simulation timeout");
        $finish;
    end

endmodule

`default_nettype wire
