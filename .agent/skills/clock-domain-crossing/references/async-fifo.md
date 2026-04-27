# Async FIFO Architecture

Gray-pointer async FIFO: architecture, depth/metastability math, and full RTL.

---

## Architecture Overview

```
Write Domain                          Read Domain
──────────────────────────────────────────────────────
wr_clk ──► [Write Logic]                    [Read Logic] ◄── rd_clk
           wr_ptr (binary)                  rd_ptr (binary)
           │                                │
           ▼ bin2gray                        ▼ bin2gray
           wr_ptr_gray                       rd_ptr_gray
           │                                │
           │ [sync_2ff to rd_clk]            │ [sync_2ff to wr_clk]
           ▼                                ▼
           wr_ptr_gray_sync (rd_clk)         rd_ptr_gray_sync (wr_clk)
           │                                │
           └──► empty logic                 └──► full logic
```

**Key property:** Gray code pointers change exactly one bit per increment, so
only one bit can be metastable at the synchronizer input. Even if that bit
resolves to the wrong value, the worst case is that the FIFO appears one entry
more full or more empty than it is — which is safe (conservative) behavior.

---

## Depth and Metastability Math

**Required FIFO depth** to absorb a burst without overflow:

```
D ≥ ceil(burst_size × (f_write / f_read))   (write-fast scenario)
D ≥ burst_size                               (write-slow, add 2–4 for latency)
```

Add 2–4 extra entries to account for the synchronizer latency (2–3 cycles of
the destination clock) before the full/empty signal updates.

**Pointer width:** For depth D, the pointer is (log2(D) + 1) bits wide. The
extra bit is used to distinguish full from empty when the binary addresses
are equal.

**MTBF of the synchronizer per pointer bit:**

```
MTBF = exp(T_resolve / τ) / (f_dst × f_src × T_w)
```

Where T_resolve = destination clock period minus setup time, τ ≈ 30–50 ps
(process-dependent), T_w = metastability window ≈ 10–20 ps. For a 4 ns
destination period, a well-characterized process gives MTBF > 10^12 years
per bit per synchronizer — safe at any reasonable system scale.

---

## Full RTL Implementation

```systemverilog
module async_fifo #(
    parameter int WIDTH = 8,
    parameter int DEPTH = 16
) (
    input  logic             wr_clk, wr_rst_n,
    input  logic [WIDTH-1:0] wr_data,
    input  logic             wr_en,
    output logic             wr_full,

    input  logic             rd_clk, rd_rst_n,
    output logic [WIDTH-1:0] rd_data,
    input  logic             rd_en,
    output logic             rd_empty
);
    localparam int AW = $clog2(DEPTH);

    logic [WIDTH-1:0]  mem [0:DEPTH-1];
    logic [AW:0]       wr_ptr_bin, rd_ptr_bin;
    logic [AW:0]       wr_ptr_gray, rd_ptr_gray;
    logic [AW:0]       wr_ptr_gray_sync, rd_ptr_gray_sync;

    // ── Write domain ──────────────────────────────────────────────────────
    always_ff @(posedge wr_clk or negedge wr_rst_n) begin
        if (!wr_rst_n)
            wr_ptr_bin <= '0;
        else if (wr_en && !wr_full) begin
            mem[wr_ptr_bin[AW-1:0]] <= wr_data;
            wr_ptr_bin <= wr_ptr_bin + 1'b1;
        end
    end

    assign wr_ptr_gray = wr_ptr_bin ^ (wr_ptr_bin >> 1);

    // ── Read domain ───────────────────────────────────────────────────────
    always_ff @(posedge rd_clk or negedge rd_rst_n) begin
        if (!rd_rst_n)
            rd_ptr_bin <= '0;
        else if (rd_en && !rd_empty)
            rd_ptr_bin <= rd_ptr_bin + 1'b1;
    end

    assign rd_data      = mem[rd_ptr_bin[AW-1:0]];
    assign rd_ptr_gray  = rd_ptr_bin ^ (rd_ptr_bin >> 1);

    // ── Cross-domain synchronizers ────────────────────────────────────────
    sync_2ff #(.WIDTH(AW+1)) u_sync_wr2rd (
        .clk_dst(rd_clk),  .rst_n(rd_rst_n),
        .d(wr_ptr_gray),   .q(wr_ptr_gray_sync)
    );

    sync_2ff #(.WIDTH(AW+1)) u_sync_rd2wr (
        .clk_dst(wr_clk),  .rst_n(wr_rst_n),
        .d(rd_ptr_gray),   .q(rd_ptr_gray_sync)
    );

    // ── Full / empty ──────────────────────────────────────────────────────
    // Empty: read gray == synchronized write gray (same address + same wrap bit)
    assign rd_empty = (rd_ptr_gray == wr_ptr_gray_sync);

    // Full: MSB and MSB-1 differ, lower bits equal (Clifford Cummings style)
    assign wr_full = (wr_ptr_gray[AW]   != rd_ptr_gray_sync[AW]  ) &&
                     (wr_ptr_gray[AW-1] != rd_ptr_gray_sync[AW-1]) &&
                     (wr_ptr_gray[AW-2:0] == rd_ptr_gray_sync[AW-2:0]);

endmodule
```

**Reference:** Clifford Cummings, "Simulation and Synthesis Techniques for
Asynchronous FIFO Design," SNUG 2002 — the definitive full/empty flag derivation.

---

## SDC Constraints for Async FIFO

```tcl
# 100 MHz write clock, 250 MHz read clock
create_clock -name wr_clk -period 10.0 [get_ports wr_clk]
create_clock -name rd_clk -period  4.0 [get_ports rd_clk]

# Declare clocks asynchronous (no common source)
set_clock_groups -asynchronous -group {wr_clk} -group {rd_clk}

# Bound gray-pointer paths to destination period (conservative: 4 ns)
# -datapath_only: excludes clock skew from analysis; tool checks data arrival only
set_max_delay 4.0 -datapath_only \
    -from [get_cells -hierarchical -filter {NAME =~ *u_sync_wr2rd*}] \
    -to   [get_cells -hierarchical -filter {NAME =~ *u_sync_wr2rd*/pipe[0]*}]

set_max_delay 10.0 -datapath_only \
    -from [get_cells -hierarchical -filter {NAME =~ *u_sync_rd2wr*}] \
    -to   [get_cells -hierarchical -filter {NAME =~ *u_sync_rd2wr*/pipe[0]*}]
```

**Why `set_max_delay -datapath_only` and not `set_false_path`:**
`set_false_path` would allow the router to use unboundedly long paths, risking a
data arrival time longer than the destination period — which is exactly the
metastability window we are trying to close. `-datapath_only` bounds the
combinational path to ≤ destination period while still excluding source-clock
skew (which is meaningless across asynchronous domains). See
`false-path-vs-max-delay.md` for full discussion.
