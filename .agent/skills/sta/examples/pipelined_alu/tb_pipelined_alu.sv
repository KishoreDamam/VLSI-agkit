//------------------------------------------------------------
// tb_pipelined_alu.sv
//
// Self-checking TB for the STA skill example.
//
// Drives identical inputs into alu_flat and alu_piped, accounting
// for the +1 cycle latency of the pipelined version, and asserts
// y_flat == y_piped_delayed.  Reports PASS / FAIL on $finish.
//
// Not a timing-analysis test in itself -- it proves functional
// equivalence, so when you study the report_timing output for
// these two modules you know they really do compute the same
// thing.
//------------------------------------------------------------
`timescale 1ns/1ps

module tb_pipelined_alu;

    localparam int W       = 8;
    localparam int N_VECS  = 200;

    logic              clk;
    logic              rst_n;
    logic [W-1:0]      a, b, c;
    logic [1:0]        op;
    logic [2*W-1:0]    y_flat;
    logic [2*W-1:0]    y_piped;

    alu_flat  #(.W(W)) u_flat  (.*, .y(y_flat));
    alu_piped #(.W(W)) u_piped (.*, .y(y_piped));

    // 1 GHz-ish clock for the example: 1 ns period
    initial clk = 1'b0;
    always #0.5 clk = ~clk;

    // alu_piped has one extra register stage -> its output is the
    // flat output delayed by 1 cycle. Track the expected value.
    logic [2*W-1:0] y_flat_d1;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            y_flat_d1 <= '0;
        else
            y_flat_d1 <= y_flat;
    end

    int n_checks;
    int n_fails;

    task automatic apply(input logic [W-1:0] aa,
                         input logic [W-1:0] bb,
                         input logic [W-1:0] cc,
                         input logic [1:0]   oo);
        @(negedge clk);
        a  = aa;
        b  = bb;
        c  = cc;
        op = oo;
    endtask

    initial begin
        rst_n = 1'b0;
        a = '0; b = '0; c = '0; op = '0;
        repeat (4) @(posedge clk);
        rst_n = 1'b1;

        // Apply N_VECS random inputs. After 2 cycles of pipeline
        // fill, sample and compare.
        for (int i = 0; i < N_VECS; i++) begin
            apply($urandom_range(0, (1<<W)-1),
                  $urandom_range(0, (1<<W)-1),
                  $urandom_range(0, (1<<W)-1),
                  $urandom_range(0, 3));
            @(posedge clk);

            // After the pipeline has filled, y_piped should match
            // y_flat_d1 (flat output delayed one cycle).
            if (i >= 3) begin
                n_checks++;
                if (y_piped !== y_flat_d1) begin
                    n_fails++;
                    $display("FAIL @ %0t  i=%0d  y_flat_d1=%h y_piped=%h",
                             $time, i, y_flat_d1, y_piped);
                end
            end
        end

        if (n_fails == 0)
            $display("PASS: %0d checks, alu_flat == alu_piped (after 1-cycle latency)",
                     n_checks);
        else
            $display("FAIL: %0d / %0d mismatches", n_fails, n_checks);

        $finish;
    end

endmodule
