// valid_ready_if.sv — Parameterized valid/ready handshake interface
// with producer and consumer modports.
//
// Interface signals:
//   clk, rst_n  — clock and active-low reset (passed in from instantiator)
//   valid        — asserted by producer when data is valid
//   ready        — asserted by consumer when it can accept data
//   data         — payload (DATA_WIDTH bits)
//
// Handshake rule: a transfer occurs when valid AND ready are both high
// on the rising edge of clk.

`default_nettype none

// ---------------------------------------------------------------------------
// Interface definition
// ---------------------------------------------------------------------------
interface valid_ready_if #(
    parameter int DATA_WIDTH = 32
) (
    input logic clk,
    input logic rst_n
);
    logic                  valid;
    logic                  ready;
    logic [DATA_WIDTH-1:0] data;

    // Producer: drives valid and data; reads ready
    modport producer (
        input  clk, rst_n,
        output valid, data,
        input  ready
    );

    // Consumer: reads valid and data; drives ready
    modport consumer (
        input  clk, rst_n,
        input  valid, data,
        output ready
    );
endinterface

// ---------------------------------------------------------------------------
// Simple producer: counts up and sends one item per cycle when ready
// Note: port uses the interface without modport specifier for iverilog
// compatibility; modport constraints are documented in the interface above.
// ---------------------------------------------------------------------------
module simple_producer #(
    parameter int DATA_WIDTH = 32
) (
    valid_ready_if bus
);
    always_ff @(posedge bus.clk or negedge bus.rst_n) begin
        if (!bus.rst_n) begin
            bus.valid <= 1'b0;
            bus.data  <= '0;
        end else begin
            bus.valid <= 1'b1;
            if (bus.valid && bus.ready)
                bus.data <= bus.data + 1;
        end
    end
endmodule

// ---------------------------------------------------------------------------
// Simple consumer: accepts data every other cycle (illustrates backpressure)
// ---------------------------------------------------------------------------
module simple_consumer #(
    parameter int DATA_WIDTH = 32
) (
    valid_ready_if bus,
    output logic [DATA_WIDTH-1:0] last_received
);
    logic accept_toggle;

    always_ff @(posedge bus.clk or negedge bus.rst_n) begin
        if (!bus.rst_n) begin
            accept_toggle <= 1'b1;
            last_received <= '0;
            bus.ready     <= 1'b1;
        end else begin
            accept_toggle <= ~accept_toggle;
            bus.ready     <= accept_toggle;
            if (bus.valid && bus.ready)
                last_received <= bus.data;
        end
    end
endmodule
