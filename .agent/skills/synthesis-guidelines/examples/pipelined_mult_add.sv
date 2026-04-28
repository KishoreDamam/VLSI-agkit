// pipelined_mult_add.sv -- Critical path optimization example
//
// Demonstrates:
//   1. Pipelining a multiply-add to fix a timing violation
//   2. Synthesis attribute usage (use_dsp, dont_touch)
//   3. Latch avoidance with default assignment in always_comb
//
// BEFORE (single-cycle, 3.2 ns path — violates 300 MHz / 3.33 ns period):
//   assign result = ($signed(a) * $signed(b)) + $signed(c);
//
// AFTER (pipelined, 1.8 ns multiply + 1.4 ns add — fits 300 MHz):
//   Stage 1: product_r <= a * b
//   Stage 2: result    <= product_r + c
//
// Synthesis: Vivado 2022.1+ or DC 2022.03+
// Lint:      iverilog -g2012 pipelined_mult_add.sv

`default_nettype none

// ---------------------------------------------------------------------------
// Parameters
// ---------------------------------------------------------------------------
// DATA_W  — operand width in bits (16 default)
// ACCUM_W — accumulator / result width; must be >= 2*DATA_W to avoid overflow

module pipelined_mult_add #(
    parameter int DATA_W  = 16,
    parameter int ACCUM_W = 32
) (
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic                 valid_in,    // input data valid
    input  logic [DATA_W-1:0]    a,           // multiply operand A
    input  logic [DATA_W-1:0]    b,           // multiply operand B
    input  logic [DATA_W-1:0]    c,           // addend
    input  logic [3:0]           opcode,      // decoder input
    output logic [ACCUM_W-1:0]   result,      // pipelined result
    output logic                 valid_out,   // result valid (2-cycle latency)
    output logic [7:0]           decoded,     // decoded control word
    // Debug observation register (preserved by dont_touch)
    output logic [ACCUM_W-1:0]   dbg_probe
);

    // -----------------------------------------------------------------------
    // Local parameters for opcode decoder
    // -----------------------------------------------------------------------
    localparam logic [3:0] OP_ADD  = 4'h0;
    localparam logic [3:0] OP_MUL  = 4'h1;
    localparam logic [3:0] OP_SUB  = 4'h2;
    localparam logic [3:0] OP_NOP  = 4'h3;

    localparam logic [7:0] ADD_CTRL = 8'hA0;
    localparam logic [7:0] MUL_CTRL = 8'hB1;
    localparam logic [7:0] SUB_CTRL = 8'hC2;
    localparam logic [7:0] NOP_CTRL = 8'h00;

    // -----------------------------------------------------------------------
    // Pipelined multiply-add
    //
    // Stage 1: multiply  (1.8 ns at 28 nm / UltraScale)
    // Stage 2: add       (1.4 ns at 28 nm / UltraScale)
    //
    // (* use_dsp = "yes" *) forces Vivado to infer a DSP48E2 for the multiply.
    // Without the attribute the tool may choose LUTs for small DATA_W.
    // -----------------------------------------------------------------------

    // Stage 1 pipeline register — force DSP inference
    (* use_dsp = "yes" *)
    logic signed [ACCUM_W-1:0] product_r;

    logic valid_s1;    // valid pipeline stage 1

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            product_r <= '0;
            valid_s1  <= 1'b0;
        end else begin
            product_r <= $signed(a) * $signed(b);
            valid_s1  <= valid_in;
        end
    end

    // Stage 2 pipeline register — add the registered product to c
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            result    <= '0;
            valid_out <= 1'b0;
        end else begin
            result    <= product_r + $signed(c);
            valid_out <= valid_s1;
        end
    end

    // -----------------------------------------------------------------------
    // Debug observation register
    //
    // (* dont_touch = "true" *) prevents Vivado from removing this register
    // during optimization (e.g., when the output is only read by an ILA probe
    // or testbench and synthesis cannot see the fanout).
    // DC equivalent: set_dont_touch [get_cells u_pipelined_mult_add/dbg_probe_r]
    // -----------------------------------------------------------------------
    (* dont_touch = "true" *)
    logic [ACCUM_W-1:0] dbg_probe_r;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) dbg_probe_r <= '0;
        else        dbg_probe_r <= result;
    end

    assign dbg_probe = dbg_probe_r;

    // -----------------------------------------------------------------------
    // Opcode decoder — latch avoidance example
    //
    // Rule: assign the default value BEFORE the case statement.
    // Without "decoded = '0" here, any opcode not listed infers a latch on
    // every bit of 'decoded'.  "unique case" adds tool-enforced coverage
    // checking but does NOT substitute for the default assignment.
    // -----------------------------------------------------------------------
    always_comb begin
        decoded = '0;              // default: prevents latch inference
        unique case (opcode)
            OP_ADD: decoded = ADD_CTRL;
            OP_MUL: decoded = MUL_CTRL;
            OP_SUB: decoded = SUB_CTRL;
            OP_NOP: decoded = NOP_CTRL;
            // All other opcodes: decoded stays '0 (from default above)
        endcase
    end

endmodule

`default_nettype wire
