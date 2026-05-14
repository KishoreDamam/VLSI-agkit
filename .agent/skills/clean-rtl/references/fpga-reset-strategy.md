# FPGA Reset Strategy — Asynchronous Assert / Synchronous Deassert

> The canonical FPGA system-reset pattern: assert async (works without
> the clock), deassert sync (guarantees recovery time). Plus the
> per-domain synchronizer requirement and the reset-type-mixing trap.

## Why all-async and all-sync both fail

Two naive approaches fail in different ways:

### Fully asynchronous reset

```systemverilog
// Both assert and deassert async
always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) q <= 0;
    else        q <= d;
```

**Problem**: at deassertion, the rising edge of `rst_n` may land too
close to the next rising clock edge. The flop's *recovery time* — a
setup-like constraint on the deassertion of the async reset — is
violated → metastable output.

Recovery time violation is silent. STA *can* check it if you constrain
the async net, but most designs don't. Functional sim doesn't show it.
The chip starts up correctly 999 times out of 1000 — the failure is a
1000-th-power-cycle anomaly.

### Fully synchronous reset

```systemverilog
// Both assert and deassert sync — clock-gated
always_ff @(posedge clk)
    if (!rst_n) q <= 0;
    else        q <= d;
```

**Problem**: the reset can only be *captured* on a rising clock edge.
If the clock is gated off (low-power mode, paused-clock debug, slow
boot-time clock), the reset never reaches the flop. Power-on with
clock not yet running → flops boot to X.

Fully-sync is fine *if* the clock is guaranteed running before reset is
asserted. That guarantee is the hard part on a real design with
clock-gating and DVFS.

## The hybrid: async assert, sync deassert

The pattern that solves both problems:

```systemverilog
module reset_sync (
    input  logic clk,
    input  logic arst_n,         // async-asserted reset in
    output logic rst_sync_n      // sync-deasserted reset out
);
    (* ASYNC_REG = "TRUE" *) logic r1, r2;

    always_ff @(posedge clk or negedge arst_n) begin
        if (!arst_n) begin
            r1 <= 1'b0;
            r2 <= 1'b0;
        end else begin
            r1 <= 1'b1;
            r2 <= r1;
        end
    end

    assign rst_sync_n = r2;
endmodule
```

What it does:

| Event | Result |
|---|---|
| `arst_n` falls (assert) | Both flops async-clear → `rst_sync_n` immediately low. No clock needed. |
| `arst_n` rises (deassert) | Flops shift `1` in synchronously over 2 cycles. Recovery time satisfied by definition. |

`r1` is the first stage — it samples a known constant `1`, so no
metastability concern. `r2` is the second stage — same.

The result `rst_sync_n` feeds the **functional reset pin** of all the
downstream flops:

```systemverilog
always_ff @(posedge clk or negedge rst_sync_n)
    if (!rst_sync_n) q <= 0;
    else             q <= d;
```

So inside the design every flop is still coded with async reset — the
flop async-clears when `rst_sync_n` falls. But `rst_sync_n` *itself*
deasserts synchronously with `clk`, so there's no recovery-time
violation downstream.

## Per-domain reset synchronizers

A design with multiple async clock domains needs **one reset
synchronizer per domain**. A single sync'd reset is sync to its own
clock, *not* to any other domain's clock:

```
                          ┌─── reset_sync(clk_a) ──→ rst_a_n  → fanout to flops on clk_a
   ext_arst_n ──┬─────────┤
                │         ├─── reset_sync(clk_b) ──→ rst_b_n  → fanout to flops on clk_b
                │         │
                │         └─── reset_sync(clk_c) ──→ rst_c_n  → fanout to flops on clk_c
                └─── all assertions are async, common edge
```

The async assertion is shared — when `ext_arst_n` falls, all
synchronizers' flops async-clear simultaneously. The sync deassertions
each occur on their own domain's next rising edge — different absolute
times for different domains, all correct in their own frame.

**Without per-domain synchronizers:** a single `rst_sync_n` (sync to
`clk_a`) feeding flops on `clk_b` is back to a recovery-time violation
on `clk_b`.

## Reset-type uniformity

A subtle pattern: even within one domain, *every flop should use the
same reset coding*. Mixing async-reset and sync-reset (or "no reset")
flops in the same pipeline blocks the synthesis retiming optimization.

```systemverilog
// ❌ Mixed reset types — blocks retiming, larger gates
always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) data_q <= 0;
    else        data_q <= d;

always_ff @(posedge clk)         // no reset clause
    out_q <= data_q;             // out_q has no reset — incompatible flop type

// ✅ Consistent — retiming works, smaller gates
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        data_q <= 0;
        out_q  <= 0;
    end else begin
        data_q <= d;
        out_q  <= data_q;
    end
end
```

See `synthesis-guidelines/references/retiming-and-register-balancing.md`
for the synthesis side of this constraint.

## Decision tree

```
Q: Will the clock always be running when reset is asserted?
   ├─ Yes → fully synchronous reset is fine.
   │
   └─ No  → use async-assert / sync-deassert pattern (this doc).

Q: Does the design have multiple async clock domains?
   ├─ Yes → one reset synchronizer per domain.
   │
   └─ No  → single synchronizer is sufficient.

Q: Does the platform need radiation hardening?
   ├─ Yes → triplicate flops + voter; reset itself triplicated.
   │
   └─ No  → single-flop reset (or hybrid above) is fine.

Q: Is power-gating used (parts of the chip lose Vdd)?
   ├─ Yes → retention flops in power-gated regions need their own reset
   │         strategy (UPF / isolation cells). See low-power-design skill.
   │
   └─ No  → standard reset is fine.
```

## Internally-generated resets

A common pattern: an internal event triggers a reset for part of the
design.

```systemverilog
// ❌ DON'T do this directly — combinational logic on async reset pin
wire internal_rst_n = ~(error_state | watchdog_timeout | sw_reset);

always_ff @(posedge clk or negedge internal_rst_n)
    if (!internal_rst_n) q <= 0;
    else                 q <= d;
```

Two problems:

- **Static-1 hazards.** If `error_state` and `watchdog_timeout` both
  change adjacent to each other, the OR can briefly glitch low →
  spurious reset edge → flops async-clear unintentionally.
- **Skew on the reset net.** The reset signal arrives at flops at
  different times based on routing → some flops see assertion before
  others → partial reset state.

**Fix:** synchronize the internal event into the clock domain and use
the result as a synchronous reset:

```systemverilog
// ✅ Synchronize internal reset trigger
logic int_rst_event;
assign int_rst_event = error_state | watchdog_timeout | sw_reset;

logic [1:0] int_rst_sync;
always_ff @(posedge clk or negedge ext_arst_n) begin
    if (!ext_arst_n) int_rst_sync <= 2'b00;
    else             int_rst_sync <= {int_rst_sync[0], int_rst_event};
end

wire effective_rst_n = ~int_rst_sync[1] & ext_arst_n;
```

The external (async) reset still asserts immediately; the internal
trigger goes through a 2-FF synchronizer and acts as a synchronous
reset to the same logic.

## Common pitfalls

- **Fully-async reset** in a design with gated/paused clocks → recovery
  time violations during reset deassertion.
- **Fully-sync reset** in a design that can power-on with the clock not
  running → flops boot to X.
- **One sync'd reset feeding multiple async clock domains** — only one
  domain is safe.
- **Mixing async and sync reset flops** within a path → retiming
  blocked, area increases.
- **Combinational logic on the async reset net** without
  synchronization → glitch-induced spurious resets.
- **Missing `ASYNC_REG` attribute** on the synchronizer flops → tool may
  optimize them away or push logic between them.
- **Reset deassertion not staggered across modules** when needed.
  Sometimes a module needs to see reset deassert N cycles before its
  neighbour for sequencing — handle with explicit deassert-counter,
  not assumed clock-skew.

## Citations

- **Kilts**, *Advanced FPGA Design*, Wiley 2007, Chapter 10 — async
  vs sync resets, hybrid pattern, multi-domain reset synchronizers.
- **Xilinx WP272** — *Get Smart About Reset: Think Local, Not Global*.
- **Cummings**, *"Asynchronous & Synchronous Reset Design Techniques,"*
  SNUG 2003.

## See also

- `synchronous-reset.md` — canonical sync-reset coding idiom and the
  `sync_set_reset` pragma.
- `simulation-race.md` — initial-always race involves reset.
- `clock-domain-crossing` skill — 2-FF synchronizer pattern that the
  reset hybrid is built from.
- `synthesis-guidelines/references/retiming-and-register-balancing.md`
  — why reset-type uniformity matters for optimization.
