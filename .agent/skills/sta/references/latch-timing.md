# Latch Timing & Time Borrowing

> Level-sensitive (transparent) latches break the simple "one-cycle window"
> model. Time borrowing lets a slow stage steal margin from the next.

## Latch vs flop semantics

| | Flip-flop (edge-triggered) | Latch (level-sensitive) |
|---|---|---|
| Data sampled | At active clock edge | While clock is at active level |
| Setup window | Before active edge | Before clock *deactivates* (closes) |
| Output behavior | Stable between edges | Transparent during active level, latched on deactive |
| Slack model | Single-cycle window | Multi-cycle borrowing possible |

A transparent latch with clock active-high holds data when CK=0 and
passes D→Q (with a small delay) when CK=1. The "capture" event is the
*falling* edge — the moment the latch closes.

## Time borrowing

If data arrives at a latch's D *after* the rising edge but *before* the
falling edge, the latch still captures it correctly — it just spends part
of the *next* phase as if the data had arrived on time.

```
clk      ___|‾‾‾‾‾‾|___|‾‾‾‾‾‾|___
                    ^
            falling edge = latch close

D arrives here:     ↑↑↑↑↑
                 valid-window
```

The "borrowed" time eats into the budget of the *next* stage. STA models
this:

- If data arrives ≤ rising edge: no borrowing, normal setup window
  (rising edge to next rising edge = full period).
- If data arrives between rising and falling: borrows (arrival - rising)
  from next stage.
- If data arrives after falling: setup violation.

Max borrow = pulse width − setup time. For a 50% duty 1 ns clock with
50 ps latch setup, max borrow is 450 ps.

## Borrow propagation

If stage N borrows X ps, stage N+1's effective setup window shrinks by X
ps. Borrowing only works if stage N+1 has at least X ps of slack — STA
will report a violation on stage N+1 if not.

This means latches form **timing chains**. STA must analyze multiple
stages together, not one path at a time. Modern tools handle this
automatically; you only need to enable it.

## SDC commands

```tcl
# Tell STA this is a level-sensitive latch (usually auto-detected from .lib)
# Not normally needed — library defines latch cells as transparent.

# Allow time borrowing up to N ps (default = pulse width - setup)
set_max_time_borrow 0.4 [get_cells lat_*]

# Disable borrowing on a specific latch
set_max_time_borrow 0 [get_cells lat_critical_*]

# Report borrowing
report_timing -delay_type max -path_type full_clock_expanded
# Look for: 'time given to startpoint' (borrowed in) and 'time borrowed
# from endpoint' (borrowed out).
```

## When to use latches

- **Datapath in high-frequency designs** — Intel x86 has used L1/L2 latch
  pipelines since the Pentium 4. Time borrowing buys ~20% Fmax over
  flop-only datapaths.
- **Async-clear-heavy designs** — latches have simpler async pre-charge
  semantics.
- **Memory peripheral logic** — SRAM data paths sometimes use latches at
  the IO boundary.

**Don't use latches when:**

- The design has clock-gating — gating + latches is fragile. Common
  enable-pulse glitches become functional bugs.
- The flow is FPGA — most FPGAs have flop-only registers; "latches"
  inferred from incomplete sensitivity lists are unintended.
- The design is automotive / safety-critical — latches make formal
  equivalence harder and audit trails longer.

## Latch inference traps (RTL)

Synthesis infers a latch when an `always_comb` block lacks a complete
assignment. This is almost always a bug:

```systemverilog
always_comb begin
  if (sel) y = a;
  // missing else — y inferred as latch !
end
```

This kind of latch:

- Has no clock — controlled by `sel`, which is data, not a clock.
- Will be flagged by lint (`clean-rtl`) and synthesis (`synthesis-guidelines`).
- Will break STA if any clock-like net drives it.

Intentional latches are instantiated cells from the library
(`LATCH_HIGH_X1` or similar), not inferred.

## Common pitfalls

- **Latch on path with `set_clock_groups -asynchronous`.** Async means no
  timing — borrowing is meaningless. The latch becomes a CDC element and
  needs a synchronizer instead.
- **Multicycle path through a latch.** Multicycle assumes a flop sample
  point; latches need separate handling (`set_max_time_borrow` or
  `set_multicycle_path -through`).
- **Borrowed time on a domain crossing.** Borrowing from a different
  clock domain is incoherent. Latches at domain boundaries must be
  explicitly synchronized.
- **Negative-edge latches treated as positive.** Library cells exist for
  both polarities; specify in instantiation, don't rely on inference.

## Reporting borrowed time

```tcl
report_timing -delay_type max -path_type full_clock_expanded \
  -nworst 10 -slack_lesser_than 1.0

# In the report look for:
#   time given to startpoint   X.XX   ← borrowed in (from previous stage)
#   time borrowed from endpoint Y.YY  ← borrowed out (to next stage)
```

## Sign-off considerations

- Foundry signoff decks often **disable borrowing** beyond N% of pulse
  width — typically 70–80% — to leave margin for latch jitter.
- POCV/AOCV interact with latch transparent windows: variation on the
  falling edge widens the borrow window's uncertainty. POCV-aware
  latch analysis is mandatory at ≤ 16 nm.
- Useful skew + latches compounds. Auditing both together is
  required — borrowed time depends on falling-edge arrival.

## See also

- `setup-hold-equations.md` — flop equations; latches add the borrow term.
- `useful-skew.md` — useful skew interacts with latch borrow windows.
- `report-timing-deepdive.md` — borrow lines in the timing report.
