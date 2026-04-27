// tb_memctl_fsm.sv — Self-checking testbench for memctl_fsm
//
// Exercises:
//   1. Read path:  IDLE → ARB → READ_ISSUE → READ_DATA → IDLE
//   2. Write path: IDLE → ARB → WRITE_ISSUE → WRITE_RESP → IDLE
//   3. busy asserts during READ_ISSUE, READ_DATA, WRITE_ISSUE, WRITE_RESP
//   4. ERROR state entry on unexpected data_valid deassertion in READ_DATA
//
// Pass/fail protocol:
//   $display("PASS"); $finish;   — all checks passed
//   $display("FAIL: reason"); $finish;  — first failure

`timescale 1ns/1ps

module tb_memctl_fsm;

    // -----------------------------------------------------------------------
    // DUT signals
    // -----------------------------------------------------------------------
    logic clk, rst_n;
    logic start, is_write, arb_sel, data_valid, resp_ready;
    logic busy, issue_read, issue_write, data_rdy, send_resp;

    // -----------------------------------------------------------------------
    // DUT instantiation
    // -----------------------------------------------------------------------
    memctl_fsm dut (
        .clk        (clk),
        .rst_n      (rst_n),
        .start      (start),
        .is_write   (is_write),
        .arb_sel    (arb_sel),
        .data_valid (data_valid),
        .resp_ready (resp_ready),
        .busy       (busy),
        .issue_read (issue_read),
        .issue_write(issue_write),
        .data_rdy   (data_rdy),
        .send_resp  (send_resp)
    );

    // -----------------------------------------------------------------------
    // Clock generation — 10 ns period (100 MHz)
    // -----------------------------------------------------------------------
    initial clk = 0;
    always #5 clk = ~clk;

    // -----------------------------------------------------------------------
    // Helper tasks
    // -----------------------------------------------------------------------
    task clk_edge(input int n);
        repeat (n) @(posedge clk);
        #1; // tiny settle after edge
    endtask

    task check(input string label, input logic actual, input logic expected);
        if (actual !== expected) begin
            $display("FAIL: %s — expected %b got %b at time %0t",
                     label, expected, actual, $time);
            $finish;
        end
    endtask

    // -----------------------------------------------------------------------
    // Test body
    // -----------------------------------------------------------------------
    initial begin
        // ------------------------------------------------------------------
        // Reset
        // ------------------------------------------------------------------
        rst_n      = 1'b0;
        start      = 1'b0;
        is_write   = 1'b0;
        arb_sel    = 1'b0;
        data_valid = 1'b0;
        resp_ready = 1'b0;

        clk_edge(3);
        rst_n = 1'b1;
        clk_edge(1);

        check("busy after reset",      busy,        1'b0);
        check("issue_read after reset", issue_read,  1'b0);
        check("issue_write after reset",issue_write, 1'b0);

        // ==================================================================
        // Test 1 — Read path: IDLE → ARB → READ_ISSUE → READ_DATA → IDLE
        // ==================================================================
        // Cycle 0: assert start; arb_sel=0 → read path
        arb_sel    = 1'b0;
        is_write   = 1'b0;
        start      = 1'b1;
        clk_edge(1);
        // After clk edge: state = ARB
        start = 1'b0;

        check("busy in ARB",        busy,        1'b1);
        check("issue_read in ARB",  issue_read,  1'b0);

        clk_edge(1);
        // state = READ_ISSUE
        check("busy in READ_ISSUE",       busy,        1'b1);
        check("issue_read in READ_ISSUE", issue_read,  1'b1);
        check("issue_write in READ_ISSUE",issue_write, 1'b0);

        // Provide data_valid in READ_DATA
        data_valid = 1'b1;
        clk_edge(1);
        // state = READ_DATA
        check("busy in READ_DATA",    busy,        1'b1);
        check("data_rdy in READ_DATA",data_rdy,    1'b1);
        check("issue_read in READ_DATA",issue_read, 1'b0);

        clk_edge(1);
        // state = IDLE (data received, cycle complete).
        // data_rdy is state-gated (only high in READ_DATA); it is 0 in IDLE
        // even if data_valid is still asserted — so order of assignment
        // vs check does not matter here.
        data_valid = 1'b0;
        check("busy in IDLE (post read)",  busy,        1'b0);
        check("data_rdy in IDLE",          data_rdy,    1'b0);

        // ==================================================================
        // Test 2 — Write path: IDLE → ARB → WRITE_ISSUE → WRITE_RESP → IDLE
        // ==================================================================
        arb_sel  = 1'b1;  // write path
        is_write = 1'b1;
        start    = 1'b1;
        clk_edge(1);
        // state = ARB
        start = 1'b0;

        check("busy in ARB (write)",       busy,        1'b1);
        check("issue_write in ARB",        issue_write, 1'b0);

        clk_edge(1);
        // state = WRITE_ISSUE
        check("busy in WRITE_ISSUE",        busy,        1'b1);
        check("issue_write in WRITE_ISSUE", issue_write, 1'b1);
        check("issue_read in WRITE_ISSUE",  issue_read,  1'b0);

        clk_edge(1);
        // state = WRITE_RESP, resp_ready not asserted yet
        check("busy in WRITE_RESP",      busy,        1'b1);
        check("send_resp in WRITE_RESP", send_resp,   1'b1);
        check("issue_write in WRITE_RESP",issue_write,1'b0);

        // Hold WRITE_RESP for one extra cycle (resp_ready still 0)
        clk_edge(1);
        check("busy held in WRITE_RESP", busy,        1'b1);
        check("send_resp held",          send_resp,   1'b1);

        // Now assert resp_ready → FSM advances to IDLE
        resp_ready = 1'b1;
        clk_edge(1);
        resp_ready = 1'b0;
        // state = IDLE
        check("busy in IDLE (post write)", busy,      1'b0);
        check("send_resp in IDLE",         send_resp, 1'b0);

        // ==================================================================
        // Test 3 — ERROR state on unexpected data_valid deassertion
        // ==================================================================
        arb_sel    = 1'b0;  // read path
        is_write   = 1'b0;
        start      = 1'b1;
        data_valid = 1'b0;  // will be low when READ_DATA is entered
        clk_edge(1);
        // state = ARB
        start = 1'b0;

        clk_edge(1);
        // state = READ_ISSUE

        // Do NOT assert data_valid → ERROR should be entered
        clk_edge(1);
        // state = READ_DATA, data_valid = 0 → next = ERROR

        clk_edge(1);
        // state = ERROR
        check("busy in ERROR",       busy,        1'b1);
        check("issue_read in ERROR", issue_read,  1'b0);
        check("data_rdy in ERROR",   data_rdy,    1'b0);

        // Stay in ERROR for a few cycles (no automatic escape)
        clk_edge(2);
        check("busy still in ERROR", busy, 1'b1);

        // Reset to escape ERROR
        rst_n = 1'b0;
        clk_edge(2);
        rst_n = 1'b1;
        clk_edge(1);
        check("busy after escape from ERROR", busy, 1'b0);

        // ==================================================================
        // All checks passed
        // ==================================================================
        $display("PASS");
        $finish;
    end

    // -----------------------------------------------------------------------
    // Timeout watchdog — prevents infinite loops in CI
    // -----------------------------------------------------------------------
    initial begin
        #10000;
        $display("FAIL: simulation timeout");
        $finish;
    end

endmodule
