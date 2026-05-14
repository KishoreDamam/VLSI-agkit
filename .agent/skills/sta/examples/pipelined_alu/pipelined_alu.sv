//------------------------------------------------------------
// pipelined_alu.sv
//
// A small datapath demonstrating *setup-slack improvement via
// pipelining*. The same combinational function is implemented two
// ways:
//
//   alu_flat    -- single-cycle, deep combinational cone (likely
//                  to fail setup at high frequency)
//   alu_piped   -- 2-stage pipelined version of the same function
//                  (same throughput, halved critical path)
//
// This file is *functional reference* for the STA skill. The
// testbench (tb_pipelined_alu.sv) exercises both and asserts
// equivalence after pipeline latency, so make verify proves the
// pipelined version is functionally identical.
//
// STA wise:  if you constrain alu_flat to a 1 ns period and run
// report_timing you will see a long critical path through the
// multiplier; alu_piped halves it. The corresponding worked
// example numbers live in references/setup-hold-equations.md.
//------------------------------------------------------------

module alu_flat #(
    parameter int W = 8
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic [W-1:0]      a,
    input  logic [W-1:0]      b,
    input  logic [W-1:0]      c,
    input  logic [1:0]        op,
    output logic [2*W-1:0]    y
);

    // Deep combinational cone:  (a * b) + (c << 2) selected by op,
    // then a final XOR-fold for the lower bits. Intentionally long
    // so it's an obvious setup-critical example.
    logic [2*W-1:0] mul_r;
    logic [2*W-1:0] add_r;
    logic [2*W-1:0] sel_r;

    always_comb begin
        mul_r = a * b;
        add_r = mul_r + (c << 2);
        unique case (op)
            2'b00: sel_r = mul_r;
            2'b01: sel_r = add_r;
            2'b10: sel_r = mul_r ^ add_r;
            2'b11: sel_r = {add_r[W-1:0], mul_r[W-1:0]};
        endcase
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            y <= '0;
        else
            y <= sel_r;
    end

endmodule


module alu_piped #(
    parameter int W = 8
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic [W-1:0]      a,
    input  logic [W-1:0]      b,
    input  logic [W-1:0]      c,
    input  logic [1:0]        op,
    output logic [2*W-1:0]    y
);

    // Stage 1: register the multiply and the shifted-c independently
    logic [2*W-1:0] mul_q;
    logic [2*W-1:0] cshift_q;
    logic [1:0]     op_q;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mul_q    <= '0;
            cshift_q <= '0;
            op_q     <= '0;
        end else begin
            mul_q    <= a * b;
            cshift_q <= c << 2;
            op_q     <= op;
        end
    end

    // Stage 2: combine and select (much shorter cone than alu_flat)
    logic [2*W-1:0] add_r;
    logic [2*W-1:0] sel_r;

    always_comb begin
        add_r = mul_q + cshift_q;
        unique case (op_q)
            2'b00: sel_r = mul_q;
            2'b01: sel_r = add_r;
            2'b10: sel_r = mul_q ^ add_r;
            2'b11: sel_r = {add_r[W-1:0], mul_q[W-1:0]};
        endcase
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            y <= '0;
        else
            y <= sel_r;
    end

endmodule
