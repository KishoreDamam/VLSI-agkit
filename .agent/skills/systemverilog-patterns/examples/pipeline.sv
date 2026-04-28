// pipeline.sv — N-stage pipeline using generate-for
//
// Parameters:
//   STAGES  : number of pipeline registers (must be >= 1)
//   WIDTH   : bit width of the data path
//
// Behavior:
//   data_out = data_in delayed by STAGES clock cycles
//   Async active-low reset clears all stages to 0

`default_nettype none
`timescale 1ns/1ps

module pipeline #(
    parameter int STAGES = 4,
    parameter int WIDTH  = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);
    // Parameter validation: STAGES must be at least 1
    initial begin
        assert (STAGES >= 1)
            else $fatal(1, "pipeline: STAGES must be >= 1, got %0d", STAGES);
    end

    // Internal stage nodes: stage[0..STAGES-1] are the register outputs.
    // Stage 0 register input = data_in.
    // Stage N-1 register output = data_out.
    logic [WIDTH-1:0] stage [0:STAGES-1];

    assign data_out = stage[STAGES-1];

    genvar i;
    generate
        for (i = 0; i < STAGES; i++) begin : gen_pipe
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n)
                    stage[i] <= '0;
                else if (i == 0)
                    stage[i] <= data_in;
                else
                    stage[i] <= stage[i-1];
            end
        end
    endgenerate

endmodule
