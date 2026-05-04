---
name: clock-domain-crossing
description: Use when a signal crosses between two asynchronous clocks, you see metastability or CDC lint warnings, designing async FIFOs or req/ack handshakes between clock domains, or writing `set_false_path`/`set_max_delay` SDC for clock-domain boundaries.
---

# Clock Domain Crossing

> Safe data transfer between asynchronous clock domains: pattern selection,
> synchronizer circuits, and timing constraints.

## When to use

- Connecting logic clocked by independent oscillators or PLL outputs.
- Bus or control signal transfers between frequency-divided or unrelated clocks.
- Reset deassertion across multiple clock domains.
- Asked about metastability, MTBF, or CDC tool violations (Spyglass, Questa CDC).
- Writing SDC constraints for async FIFO pointers or handshake buses.

## Quick reference

| Signal type | Recommended pattern | Anti-pattern |
|---|---|---|
| Single control bit | 2-FF synchronizer | Direct connection (no sync) |
| Slow-changing single bit | 2-FF synchronizer | Latch in destination domain |
| Multi-bit bus, any rate | Async FIFO (gray pointer) | 2-FF on raw binary bus |
| Single multi-bit sample, slow src | Req/ack handshake | 2-FF on each bus bit |
| Single pulse, any ratio | Pulse synchronizer (toggle) | Short pulse direct to fast domain |
| Reset deassertion | Per-domain reset synchronizer | Global async reset net |
| Gray counter / one-hot | 2-FF with WIDTH > 1 | Binary counter through sync |

## Core patterns

### 2-FF Synchronizer (single-bit)

- **Use when:** crossing a single control bit, valid/enable, interrupt, or
  Gray-coded/one-hot signal between asynchronous domains.
- **Code:**

  ```systemverilog
  module sync_2ff #(
      parameter int WIDTH  = 1,
      parameter int STAGES = 2
  ) (
      input  logic             clk_dst, rst_n,
      input  logic [WIDTH-1:0] d,
      output logic [WIDTH-1:0] q
  );
      (* ASYNC_REG = "TRUE" *)
      logic [STAGES-1:0][WIDTH-1:0] pipe;

      always_ff @(posedge clk_dst or negedge rst_n) begin
          if (!rst_n) pipe <= '0;
          else begin
              pipe[0] <= d;
              for (int i = 1; i < STAGES; i++) pipe[i] <= pipe[i-1];
          end
      end
      assign q = pipe[STAGES-1];
  endmodule
  ```

- **Gotchas:**
  - `(* ASYNC_REG = "TRUE" *)` is mandatory for Vivado; without it, the tool
    may insert logic between FF stages or optimize them away.
  - Set `STAGES = 3` for destination clocks above ~500 MHz or safety-critical
    designs; each stage exponentially improves MTBF.
  - `WIDTH > 1` is only safe for Gray-coded or one-hot signals. Never use
    `WIDTH > 1` for an arbitrary binary bus — bits resolve metastability
    independently and can produce transient garbage values.

> Full module code, 3-FF variant, synthesis attributes for DC/Genus, and
> pulse synchronizer circuit: `references/synchronizer-circuits.md`.

---

### Why 2-FF Fails on Multi-bit Buses

The failure mode is bit-skew metastability:

1. Each bit of the bus has its own metastability event, independent of the others.
2. If two or more bits are simultaneously metastable, they resolve to their
   final values at different times within the same destination clock cycle.
3. The destination domain samples a transient combination that was never a valid
   source value — a "ghost" state.

**Example:** binary counter 0111 → 1000 has all 4 bits changing at once.
Even if the source change is gradual, the destination samples some bits at 0111
and others at 1000, producing 0000, 0001, 0110, 1010 … etc. transiently.

**Safe alternatives for multi-bit:**
- **Gray code:** only one bit changes per increment → at most one metastable bit.
- **Async FIFO:** encodes pointers as Gray code internally; data is never directly
  synchronized.
- **Req/ack handshake:** source holds data stable; destination samples only after
  the req signal (1-bit) has been synchronized and confirmed stable.

---

### Async FIFO (multi-bit bus or stream)

- **Use when:** transferring a bus or stream where both sides run independently
  and the data rate is non-trivial (more than occasional samples).
- **Code snippet (instantiation):**

  ```systemverilog
  async_fifo #(.WIDTH(32), .DEPTH(16)) u_cdc_fifo (
      .wr_clk  (clk_50),   .wr_rst_n(rst_50_n),
      .wr_data (data_src), .wr_en   (valid_src),
      .wr_full (fifo_full),
      .rd_clk  (clk_200),  .rd_rst_n(rst_200_n),
      .rd_data (data_dst), .rd_en   (ready_dst),
      .rd_empty(fifo_empty)
  );
  ```

- **Gotchas:**
  - Depth must absorb burst size plus 2–4 entries for synchronizer latency.
  - Write and read resets must deassert synchronously to their respective
    clocks (use `reset_sync` for each).
  - The full/empty flags are conservative by up to `STAGES` cycles due to
    pointer synchronization delay — design around this.

> Full RTL (gray-pointer, full/empty derivation), depth math, and SDC:
> `references/async-fifo.md`.

---

### Req/Ack Handshake (single multi-bit sample)

- **Use when:** sending one multi-bit configuration register or status snapshot
  infrequently. Simpler than a FIFO when throughput is low.
- **Code sketch:**

  ```systemverilog
  // Source: register data, assert req; hold until ack returns
  always_ff @(posedge clk_src or negedge rst_src_n) begin
      if (!rst_src_n) begin data_hold <= '0; req_src <= 1'b0; end
      else if (src_send && !src_busy) begin
          data_hold <= src_data; req_src <= 1'b1;
      end else if (ack_src_sync) req_src <= 1'b0;
  end

  // Destination: sync req, sample data on rising edge, assert ack
  sync_2ff u_req_sync (.clk_dst(clk_dst), .rst_n(rst_dst_n),
                       .d(req_src), .q(req_dst_sync));
  ```

- **Gotchas:**
  - Source must hold `req` asserted until ack returns — typically 4–6 destination
    cycles round-trip.
  - For fast-to-slow crossing (e.g. 500 MHz → 10 MHz): source must hold `req`
    stable for at least `ceil(T_dst / T_src) + 1` source cycles so the
    destination can sample it cleanly. Example: 500 MHz src / 10 MHz dst →
    hold for `ceil(100 ns / 2 ns) + 1 = 51` source cycles minimum.
  - Data path SDC: `set_max_delay -datapath_only ≤ T_dst` from `data_hold` to
    destination capture FF.

> Full RTL with timing diagram, slow-to-fast and fast-to-slow variants,
> min-pulse-width analysis: `references/handshake-cdc.md`.

---

### Reset Synchronizer

- **Use when:** async reset net crosses clock domains — per domain, one instance.
- **Code:**

  ```systemverilog
  module reset_sync (
      input  logic clk_dst, async_rst_n,
      output logic sync_rst_n
  );
      (* ASYNC_REG = "TRUE" *)
      logic [1:0] rst_pipe;
      always_ff @(posedge clk_dst or negedge async_rst_n) begin
          if (!async_rst_n) rst_pipe <= 2'b00;
          else              rst_pipe <= {rst_pipe[0], 1'b1};
      end
      assign sync_rst_n = rst_pipe[1];
  endmodule
  ```

- **Gotchas:**
  - Async **assert** (D=0 path) is asynchronous by design — CDC tools will flag it.
    Add a waiver: `waive -rule CDC_RESET_SIGNAL -comment "async assert by design"`.
  - SDC: `set_false_path -to [get_pins .../rst_pipe[0]/D]` on the first-stage D pin.
  - Three clock domains → three `reset_sync` instances, each with its own clock.

## Anti-patterns (do NOT do this)

1. **2-FF on a raw binary bus.** Bits resolve metastability independently;
   transient garbage values are guaranteed under any frequency ratio.
2. **`set_false_path` on FIFO gray-pointer paths.** Leaves routing unconstrained;
   the router may use a path longer than the destination period, defeating the
   synchronizer. Use `set_max_delay -datapath_only` instead.
3. **Single global async reset net.** Reset deassertion is asynchronous to all
   receiving clocks; use a `reset_sync` instance per domain.
4. **Narrow pulse into a fast domain without a toggle/pulse-sync.** A 1-cycle
   pulse in a slow domain (e.g., 100 ns at 10 MHz) may be entirely missed by a
   fast domain sampling at 2 ns intervals if it arrives in a blind spot.
5. **Hardcoded synchronizer depth (magic number `2`).** Use a parameter so
   designers can raise to 3 at a single call site for high-speed targets.
6. **Omitting `ASYNC_REG` (or equivalent) attribute.** Synthesis tools may
   retime or merge the synchronizer FFs, destroying the metastability property.

## Validation checklist (before declaring code "done")

- [ ] Every signal crossing a clock domain uses an explicit synchronization
      primitive (2-FF, async FIFO, handshake, or pulse sync).
- [ ] No `WIDTH > 1` 2-FF synchronizer on an arbitrary binary bus.
- [ ] `ASYNC_REG = "TRUE"` (or tool-equivalent) on every synchronizer FF chain.
- [ ] One `reset_sync` instance per destination clock domain.
- [ ] FIFO depth accounts for synchronizer latency (add 2–4 entries).
- [ ] SDC: gray-pointer paths use `set_max_delay -datapath_only`, not `set_false_path`.
- [ ] CDC tool (Spyglass / Questa CDC) reports no unwaived violations.
- [ ] Spyglass waiver for async reset assert path is documented with rationale.

## Citations

- **IEEE 1800-2017 §4.10** — defines timing of asynchronous resets; basis for
  "async assert, synchronous deassert" as the normative handling pattern.
- **SDC 1.9 (Synopsys SDC Reference Manual)** — defines `-datapath_only` flag
  semantics for `set_max_delay`; implemented identically in Vivado and Innovus.

## See also

- `references/synchronizer-circuits.md` — 2-FF, 3-FF, reset sync, pulse sync;
  full module code and MTBF discussion. Read when tuning STAGES or implementing
  a pulse synchronizer.
- `references/async-fifo.md` — gray-pointer FIFO RTL, depth/metastability math,
  and SDC templates. Read when instantiating or writing an async FIFO.
- `references/handshake-cdc.md` — full req/ack RTL, timing diagram, slow-to-fast
  and fast-to-slow variants. Read when crossing a single multi-bit value.
- `references/false-path-vs-max-delay.md` — SDC tradeoff analysis with examples.
  Read before writing any CDC timing exception.
- `examples/sync_2ff.sv` — parameterized 2-FF synchronizer module (buildable).
- `examples/tb_sync_2ff.sv` — self-checking testbench; run with `make verify`.
