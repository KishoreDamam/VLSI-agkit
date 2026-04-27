# Req/Ack Handshake CDC

Full req/ack handshake for transferring a multi-bit value across clock domains.
Safe for any frequency ratio, including slow-to-fast and fast-to-slow.

---

## Protocol Overview

```
clk_src:  _____|‾|_____________|‾|___
data_src:  ====X=====DATA=====X======
req_src:  ______|‾‾‾‾‾‾‾‾‾‾‾‾|______
                     (sync 2 cycles)
req_dst:  ___________|‾‾‾‾‾‾‾‾|_____
data_dst:  =========|====DATA===|====   ← sample here
ack_dst:  _______________|‾‾‾‾‾|____
                     (sync 2 cycles)
ack_src:  ___________________|‾‾|___
req_src:  cleared when ack_src seen
```

**Rules:**
1. Source registers `data` and asserts `req`. Data must remain stable until ack.
2. Destination synchronizes `req`; when seen, samples `data`, asserts `ack`.
3. Source synchronizes `ack`; when seen, clears `req`.
4. Destination synchronizes the cleared `req`; when seen, clears `ack`.
5. Next transfer may begin only after step 4 completes.

---

## RTL — Slow-to-Fast (10 MHz → 500 MHz example)

```systemverilog
module handshake_cdc #(
    parameter int WIDTH = 16
) (
    // Source domain (clk_src, e.g. 10 MHz)
    input  logic             clk_src, rst_src_n,
    input  logic [WIDTH-1:0] src_data,
    input  logic             src_send,   // 1-cycle "send" pulse from user
    output logic             src_busy,   // high while transfer in progress

    // Destination domain (clk_dst, e.g. 500 MHz)
    input  logic             clk_dst, rst_dst_n,
    output logic [WIDTH-1:0] dst_data,
    output logic             dst_valid   // 1-cycle valid in dst domain
);
    // ── Source domain ──────────────────────────────────────────────────
    logic [WIDTH-1:0] data_hold;
    logic req_src, ack_src_sync;

    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n) begin
            data_hold <= '0;
            req_src   <= 1'b0;
        end else begin
            if (src_send && !src_busy) begin
                data_hold <= src_data;
                req_src   <= 1'b1;
            end else if (ack_src_sync) begin
                req_src   <= 1'b0;
            end
        end
    end

    assign src_busy = req_src;

    sync_2ff #(.WIDTH(1)) u_ack_sync (
        .clk_dst(clk_src), .rst_n(rst_src_n),
        .d(ack_dst_reg), .q(ack_src_sync)
    );

    // ── Destination domain ─────────────────────────────────────────────
    logic req_dst_sync, req_dst_d;
    logic ack_dst_reg;

    sync_2ff #(.WIDTH(1)) u_req_sync (
        .clk_dst(clk_dst), .rst_n(rst_dst_n),
        .d(req_src), .q(req_dst_sync)
    );

    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n) begin
            req_dst_d  <= 1'b0;
            ack_dst_reg <= 1'b0;
            dst_data    <= '0;
        end else begin
            req_dst_d <= req_dst_sync;
            if (req_dst_sync && !req_dst_d) begin  // rising edge of synced req
                dst_data    <= data_hold;           // sample stable data
                ack_dst_reg <= 1'b1;
            end else if (!req_dst_sync) begin
                ack_dst_reg <= 1'b0;
            end
        end
    end

    assign dst_valid = req_dst_sync && !req_dst_d;

endmodule
```

---

## Minimum Pulse Width Constraint

For `src_send` to be reliably captured, it must be held for at least 1 full
`clk_src` cycle (standard single-cycle pulse). The protocol then holds `req_src`
stable until `ack` returns — no further pulse-width concern after that.

For a slow-to-fast crossing (10 MHz → 500 MHz), the req signal held in the
slow domain (100 ns cycle) will be sampled by the fast destination (2 ns cycle)
with 50× oversampling — no minimum-pulse-width issue.

For fast-to-slow crossings, the source must hold `req` asserted for at least
`2 × T_dst + setup_time` before the destination can see it. With a toggle/
pulse-sync approach for fast-to-slow, use the pulse synchronizer in
`synchronizer-circuits.md` instead.

---

## SDC for Handshake Data Bus

The `data_hold` register is stable when the destination samples it (by protocol).
Use `set_max_delay -datapath_only` to bound the path, not `set_false_path`:

```tcl
# Bound data path from source register to destination sampling FF
set_max_delay 2.0 -datapath_only \
    -from [get_cells -hierarchical -filter {NAME =~ *data_hold*}] \
    -to   [get_cells -hierarchical -filter {NAME =~ *dst_data*}]
```

The 2.0 ns bound should be ≤ the destination clock period (500 MHz → 2 ns).
