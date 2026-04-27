// memctl_fsm.sv — Seven-state memory controller FSM
//
// Demonstrates three-process style:
//   Process 1: sequential state register (async active-low reset)
//   Process 2: combinational next-state logic
//   Process 3: combinational output logic
//
// All outputs assigned in every branch (defaults before case) — no latches.
// One-hot encoding values; case matches on named enum labels (iverilog-compatible).

`timescale 1ns/1ps

module memctl_fsm (
    input  logic clk,
    input  logic rst_n,       // active-low async reset
    input  logic start,       // initiate a new transaction
    input  logic is_write,    // 1 = write, 0 = read (unused directly; arb_sel drives path)
    input  logic arb_sel,     // round-robin arbiter grant (1 = write wins, 0 = read wins)
    input  logic data_valid,  // read data available from downstream
    input  logic resp_ready,  // upstream ready to accept write response
    output logic busy,        // transaction in progress
    output logic issue_read,  // issue read command downstream
    output logic issue_write, // issue write command downstream
    output logic data_rdy,    // read data forwarded to upstream
    output logic send_resp    // write response forwarded to upstream
);

    // -----------------------------------------------------------------------
    // State encoding — one-hot, 7 states
    // Explicit bit-vector constants; matched via enum label in case statements.
    // -----------------------------------------------------------------------
    typedef enum logic [6:0] {
        IDLE        = 7'b000_0001,
        ARB         = 7'b000_0010,
        READ_ISSUE  = 7'b000_0100,
        READ_DATA   = 7'b000_1000,
        WRITE_ISSUE = 7'b001_0000,
        WRITE_RESP  = 7'b010_0000,
        ERROR       = 7'b100_0000
    } state_t;

    state_t state, next_state;

    // -----------------------------------------------------------------------
    // Process 1: State register — async reset, synchronous update
    // -----------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end

    // -----------------------------------------------------------------------
    // Process 2: Combinational next-state logic
    //
    // Round-robin arbiter: arb_sel input selects read (0) or write (1).
    // ERROR state: entered when data_valid deasserts unexpectedly during
    //              READ_DATA; held until reset (no automatic escape).
    // -----------------------------------------------------------------------
    always_comb begin
        next_state = state;   // default: hold current state

        case (state)
            IDLE: begin
                if (start)
                    next_state = ARB;
                else
                    next_state = IDLE;
            end

            ARB: begin
                // Round-robin dispatch based on arb_sel
                if (arb_sel)
                    next_state = WRITE_ISSUE;
                else
                    next_state = READ_ISSUE;
            end

            READ_ISSUE: begin
                // Command issued; advance to receive data next cycle
                next_state = READ_DATA;
            end

            READ_DATA: begin
                if (!data_valid)
                    next_state = ERROR;     // unexpected deassertion → error
                else
                    next_state = IDLE;      // data received, return to idle
            end

            WRITE_ISSUE: begin
                // Command issued; advance to response phase
                next_state = WRITE_RESP;
            end

            WRITE_RESP: begin
                if (resp_ready)
                    next_state = IDLE;
                else
                    next_state = WRITE_RESP;
            end

            ERROR: begin
                // Held until reset — no automatic escape
                next_state = ERROR;
            end

            default: next_state = IDLE;
        endcase
    end

    // -----------------------------------------------------------------------
    // Process 3: Combinational output logic
    //
    // All outputs assigned in defaults section first, then overridden per
    // state. This guarantees zero latches regardless of which states are
    // active.
    // -----------------------------------------------------------------------
    always_comb begin
        // Defaults — all outputs deasserted
        busy        = 1'b0;
        issue_read  = 1'b0;
        issue_write = 1'b0;
        data_rdy    = 1'b0;
        send_resp   = 1'b0;

        case (state)
            IDLE: begin
                // No outputs active in idle
            end

            ARB: begin
                busy = 1'b1;
            end

            READ_ISSUE: begin
                busy       = 1'b1;
                issue_read = 1'b1;
            end

            READ_DATA: begin
                busy     = 1'b1;
                data_rdy = data_valid;  // forward valid data only
            end

            WRITE_ISSUE: begin
                busy        = 1'b1;
                issue_write = 1'b1;
            end

            WRITE_RESP: begin
                busy      = 1'b1;
                send_resp = 1'b1;
            end

            ERROR: begin
                // busy signals the stuck condition upstream
                busy = 1'b1;
            end

            default: begin
                // Defaults already applied above
            end
        endcase
    end

endmodule
