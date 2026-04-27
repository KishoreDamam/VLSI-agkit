// sync_2ff.sv — Parameterized multi-stage synchronizer
`timescale 1ns/1ps
//
// Primary use case: single-bit (WIDTH=1) crossing between asynchronous clock domains.
// WIDTH > 1 is safe ONLY for Gray-coded or one-hot signals where at most one bit
// changes per source-clock cycle. Never use WIDTH > 1 for arbitrary binary buses.
//
// Synthesis attributes:
//   Vivado  : (* ASYNC_REG = "TRUE" *) on pipe — place adjacent FFs, no logic insertion
//   DC/Genus: add set_dont_touch / dont_touch on the synchronizer cells in scripts

`default_nettype none

module sync_2ff #(
    parameter int WIDTH  = 1,  // signal width; see WIDTH > 1 warning above
    parameter int STAGES = 2   // synchronizer depth; use 3 for f_dst > 500 MHz
) (
    input  logic             clk_dst,  // destination clock
    input  logic             rst_n,    // async active-low reset (destination domain)
    input  logic [WIDTH-1:0] d,        // asynchronous input
    output logic [WIDTH-1:0] q         // synchronized output (clk_dst domain)
);

    (* ASYNC_REG = "TRUE" *)
    logic [STAGES-1:0][WIDTH-1:0] pipe;

    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n) begin
            pipe <= '0;
        end else begin
            pipe[0] <= d;
            for (int i = 1; i < STAGES; i++) begin
                pipe[i] <= pipe[i-1];
            end
        end
    end

    assign q = pipe[STAGES-1];

endmodule

`default_nettype wire
