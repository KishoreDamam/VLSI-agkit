# Combinational Paths — Feedthroughs and Point-to-Point Exceptions

> Paths that pass through a block without being captured. They need their
> own arrival and required-time budgets, distributed across the path's
> consecutive blocks.

## What a combinational path is

A path that starts at an input port and ends at an output port —
*without* passing through a register inside the block. In a hierarchical
design, such paths are common: a control signal hops through multiple
blocks before reaching its eventual flop.

```
   Source              Destination
    ──→ B1 ──→ B2 ──→ B3 ──→ B4 ──→
        (I1)        (I3 O3)
```

In each block, the signal enters one input and exits one output with no
register in between. STA must time the *entire* end-to-end path against
some total budget — but each block sees only its slice of the design.

## Feedthrough — straight wire through a block

A specific kind of combinational path: the block's `output[k]` is
directly connected to `input[k]` (often through an inverter, buffer, or
sometimes literally a wire). The block does nothing to the signal
beyond passing it through.

```
   I1 ─────────────────────── O1   (feedthrough — same logical signal)
   I2 ──┐
        AND ── flop ── O2          (regular registered path)
   I3 ──┘
```

Two reasons feedthroughs exist:

1. **Routing relief** — a hard macro / IP block lets external signals
   route *through* its body, avoiding the detour around its edges. See
   `synthesis-guidelines/references/congestion-aware-rtl.md`.
2. **Pin reuse** — the block exposes a signal it doesn't process, so
   higher hierarchy can route through it.

The book and SDC literature use "feedthrough" specifically for these
straight-through paths, separate from the Verilog/VHDL "feedthrough"
where data overshoots a register stage (covered in
`clean-rtl/references/simulation-race.md` if added).

## The budget problem

End-to-end target: `S → D` must arrive within 13 ns. Path crosses 4
blocks; each block has 2 ns internal budget; flight time between blocks
is 1 ns.

```
S → 1ns → B1(2ns) → 1ns → B2(2ns) → 1ns → B3(2ns) → 1ns → B4(2ns) → 1ns → D
└──────────────────────────── 13ns ──────────────────────────────┘
```

Each block needs:

- `set_input_delay` — how long it took to get to the input port from
  the original source.
- `set_output_delay` — how long it will still take from the output port
  to the destination.

Computed budget per block:

| Block | input_delay | output_delay | internal budget |
|---|---|---|---|
| B1 | 1.0  (source→I1) | 10.0 (O1→D: 3 blocks × 2 + 4 flights × 1) | 13 - 1 - 10 = 2 |
| B2 | 4.0  (1 block × 2 + 2 flights × 1) | 7.0 | 2 |
| B3 | 7.0 | 4.0 | 2 |
| B4 | 10.0 | 1.0 | 2 |

```tcl
# B1
set_input_delay  -max -clock CLK  1.0  [get_ports I1]
set_output_delay -max -clock CLK 10.0  [get_ports O1]

# B2
set_input_delay  -max -clock CLK  4.0  [get_ports I2]
set_output_delay -max -clock CLK  7.0  [get_ports O2]

# B3
set_input_delay  -max -clock CLK  7.0  [get_ports I3]
set_output_delay -max -clock CLK  4.0  [get_ports O3]

# B4
set_input_delay  -max -clock CLK 10.0  [get_ports I4]
set_output_delay -max -clock CLK  1.0  [get_ports O4]
```

Sum of `input_delay + internal + output_delay` equals the total period
(13 ns) for every block. Each block independently sees enough constraint
to meet its 2 ns slice.

## `set_max_delay` vs `set_input_delay`/`set_output_delay`

Two ways to constrain a combinational path:

```tcl
# Approach 1 — max_delay direct
set_max_delay 2.0 -from [get_ports I2] -to [get_ports O2]

# Approach 2 — distributed input/output_delay (preferred)
set_input_delay  -max -clock CLK 4.0 [get_ports I2]
set_output_delay -max -clock CLK 7.0 [get_ports O2]
```

**Why approach 2 is usually preferred:**

1. **Composability.** The block's SDC describes its *interface*; the
   top-level SDC describes how the blocks compose. If each block uses
   its own `set_max_delay`, no top-level view of the full path exists.
2. **Same SDC drives synth and STA.** Approach 2 is the natural form
   for hierarchical synthesis; the same SDC works in both.
3. **Tool-uniform interpretation.** `set_max_delay` between ports has
   subtle interactions with `set_input_delay` already on those ports.

**When `set_max_delay` is right:**

- Constraints that don't follow the clock-aligned model (e.g., specific
  point-to-point timing requirements not tied to a clock).
- Asynchronous interfaces where there's no natural reference clock.
- CDC max-delay constraints (`set_max_delay -datapath_only`).

## Imperfect block-internal budgets

Reality: blocks rarely meet exactly their nominal budget. B2 needs 2.5
ns instead of 2.0; B4 fits in 1.5 ns. The total still meets 13 ns, but
the per-block input/output_delay must shift to absorb the imbalance.

Two strategies:

### Strategy A — propagate actual times

Update each downstream block's `set_input_delay` to reflect B2's
overrun:

```tcl
# B2 took 2.5 ns instead of 2.0 → 0.5 ns later than expected
set_input_delay -max -clock CLK 7.5 [get_ports I3]   ;# was 7.0
set_input_delay -max -clock CLK 10.5 [get_ports I4]  ;# was 10.0
set_output_delay -max -clock CLK 6.5 [get_ports O2]  ;# tightened
```

Faithful to reality. Downside: every block boundary shifts, and the
SDC for blocks like B3 (which didn't change internally) becomes
out-of-sync with its actual delay.

### Strategy B — "shift the budget" silently

Keep B3's SDC unchanged; just tighten B2's `set_output_delay` and
loosen B4's `set_input_delay` to absorb the slack swap:

```tcl
# B2: 2.5 ns internal → 0.5 ns tighter output budget
set_input_delay  -max -clock CLK 4.0 [get_ports I2]   ;# unchanged
set_output_delay -max -clock CLK 6.5 [get_ports O2]   ;# was 7.0

# B4: 1.5 ns internal → 0.5 ns more time on input arrival
set_input_delay  -max -clock CLK 10.5 [get_ports I4]  ;# was 10.0
set_output_delay -max -clock CLK 1.0  [get_ports O4]  ;# unchanged
```

The set_input_delay no longer reflects "real arrival time" — it
reflects "what B4 is allowed to assume." This is common practice on
high-performance designs where many blocks share feedthroughs. Trade:
fewer SDC edits when one block changes, but the SDC no longer documents
true arrival times.

Most teams pick Strategy B and document the convention in the SDC
guidance.

## Point-to-point exceptions

`set_min_delay` and `set_max_delay` are the SDC commands for explicit
point-to-point timing. Unlike `set_input_delay` / `set_output_delay`
which are tied to a reference clock, these constrain raw delay.

```tcl
# Max delay 2.0 ns regardless of clock
set_max_delay 2.0 -from [get_ports I1] -to [get_ports O1]

# CDC-style: bound the gray-pointer datapath without clock-skew analysis
set_max_delay 4.0 -datapath_only \
    -from [get_pins wr_ptr_gray*/Q] \
    -to   [get_pins rd_sync*/D]

# Min delay (rare; usually for skew matching)
set_min_delay 0.5 -from [get_ports clk_a] -to [get_pins delay_match_buf/A]
```

Common applications:

- **Async I/F**: bus to async peripheral; no clock to reference, just a
  flight-time budget.
- **CDC datapath**: `set_max_delay -datapath_only` (gray pointers,
  req/ack).
- **Clock-skew matching**: enforce a delay on a deskew buffer.
- **DDR strobe alignment**: tightly bound delays for source-synchronous
  paths.

## Path breaking

Sometimes a path exists structurally but the design relies on it being
*broken* — e.g., a sleep-mode latch breaks the data path. SDC
`set_disable_timing` removes a specific arc:

```tcl
set_disable_timing [get_cells sleep_latch] -from D -to Q
```

Use sparingly — disable_timing is opaque and easy to forget. Prefer
case analysis when the break is mode-conditional.

## Common pitfalls

- **Unconstrained feedthroughs.** No `set_input_delay`/`set_output_delay`
  → tool assumes infinite slack on the path → it under-optimizes the
  block-internal portion. Audit with `check_timing`.
- **set_max_delay on a path that's also constrained by input/output_delay.**
  Tool may use the tighter of the two; behaviour varies tool to tool.
- **Forgetting `-datapath_only` on CDC max-delay.** Tool includes
  clock-skew analysis on an async path, which is incoherent.
- **Hierarchical budget that doesn't sum.** Sum of all per-block
  input+internal+output budgets should equal the end-to-end target.
  Off-by-one is the most common SDC bug on feedthroughs.
- **Path that exists only after synthesis optimization.** Synthesis may
  flatten or merge logic, creating new combinational paths that no SDC
  ever described. Re-run `check_timing` on the post-synthesis netlist.

## Validation

```tcl
# Identify combinational paths
report_timing -from [all_inputs] -to [all_outputs] -nworst 20

# Verify feedthroughs are constrained
check_timing -include {no_input_delay no_output_delay}

# Path-budget sanity
report_timing -path_type full -from <input> -to <output>
```

## Citations

- **SDC 1.9** — `set_max_delay`, `set_min_delay`, `set_disable_timing`.
- **Gangadharan & Churiwala**, *Constraining Designs for Synthesis and
  Timing Analysis* (Springer 2013), Chapter 13.

## See also

- `io-delays.md` — `set_input_delay` / `set_output_delay` mechanics.
- `false-paths-catalog.md` — exception patterns for unsensitizable
  combinational paths.
- `clock-domain-crossing` skill — `set_max_delay -datapath_only` for
  CDC.
- `synthesis-guidelines/references/congestion-aware-rtl.md` —
  feedthroughs at the physical level.
