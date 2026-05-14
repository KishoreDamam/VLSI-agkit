# Clock Uncertainty

> What `set_clock_uncertainty` actually budgets, and how to build a defensible
> value from PLL jitter, clock-tree skew, and design margin.

## What uncertainty is

`set_clock_uncertainty` is a single number (per clock, per setup/hold) that
the STA tool subtracts from the available timing budget. It models effects
the STA engine does not natively simulate:

1. **PLL jitter** — random and deterministic variation in the source clock.
2. **Power-supply noise** — induced clock-arrival variation.
3. **Estimated CTS skew** — pre-CTS placeholder for skew the engine cannot
   yet measure (post-CTS, set to actual measured skew).
4. **Design margin** — engineering safety factor.

After CTS, the **measured skew** becomes part of the clock-network analysis
itself, so you reduce uncertainty to cover only the *remaining* effects
(jitter + margin).

## Pre-CTS vs post-CTS budgets

| Phase | Setup uncertainty | Hold uncertainty |
|---|---|---|
| Pre-synth / pre-CTS | 200–400 ps (covers est. skew + jitter + margin) | 50–150 ps |
| Post-CTS | 50–150 ps (jitter + margin only) | 30–80 ps |
| Sign-off | Per foundry signoff deck | Per foundry signoff deck |

```tcl
# Pre-CTS budget for a 1 GHz clock
set_clock_uncertainty -setup 0.250 [get_clocks clk_core]
set_clock_uncertainty -hold  0.080 [get_clocks clk_core]

# Post-CTS, after CTS has resolved actual skew
set_propagated_clock [get_clocks clk_core]
set_clock_uncertainty -setup 0.100 [get_clocks clk_core]
set_clock_uncertainty -hold  0.050 [get_clocks clk_core]
```

## Jitter components

A real PLL has three measurable jitter species. Budget them additively
(setup) or RSS-style if you have characterization data:

| Type | What it is | Affects |
|---|---|---|
| **Period jitter** | Edge-to-edge period variation | Setup (one cycle) |
| **Cycle-to-cycle** | Variation between consecutive periods | Setup, hold |
| **Long-term (accumulated)** | Drift over many cycles | Multi-cycle paths, async FIFOs |

For PLL-locked sync designs, period jitter dominates setup uncertainty.
For SSC (spread-spectrum) designs, long-term drift matters too.

Typical PLL data-sheet numbers:

- Cell-based PLL on 28 nm: ±30 ps period jitter, ±50 ps long-term.
- LCPLL / fractional-N: ±10 ps period, ±20 ps long-term.

## Skew vs uncertainty — they are different

Skew is **arrival-time difference between two CK pins** of a real clock
tree. It is computed by the STA engine from the netlist + parasitics.

Uncertainty is **everything STA cannot compute** — declared by the user.

When you set `set_propagated_clock`, the engine replaces idealized clock
skew with the actual computed skew. Uncertainty should then *only* cover
jitter + margin. Forgetting to reduce uncertainty after propagating
clocks is one of the most common over-margin sources.

## Setup vs hold uncertainty — why different

Setup needs to cover the **slow-edge** scenario: launch clock arrives
late, capture arrives early — uncertainty is added pessimistically.

Hold needs to cover the **race** scenario: launch arrives early, capture
late, *and* logic delay is at minimum. Hold uncertainty is usually
smaller because:

- Jitter on the same cycle (launch and capture) is partially correlated.
- CTS skew is bounded by the actual tree, not estimated.

Foundry signoff decks specify these separately — don't use a single
combined value.

## Per-clock-pair uncertainty (for sync clocks)

When two synchronous clocks interact, you can refine the budget per pair:

```tcl
# Inter-clock setup margin
set_clock_uncertainty -setup -from [get_clocks clk_a] -to [get_clocks clk_b] 0.150

# Hold from clk_b launches to clk_a captures
set_clock_uncertainty -hold  -from [get_clocks clk_b] -to [get_clocks clk_a] 0.060
```

This is essential when one clock has worse jitter than the other (e.g.,
an external SerDes recovered clock vs an on-chip PLL).

## Asymmetric setup/hold trade-off

You can also use uncertainty to model a **non-50% duty cycle effect**
without changing `create_clock`:

```tcl
# Effective 45/55 duty: reduce setup window, expand hold window
set_clock_uncertainty -setup 0.100 [get_clocks clk_core]
set_clock_uncertainty -hold  0.100 [get_clocks clk_core]   ;# both wider
```

Better: declare actual waveform on `create_clock -waveform`. Uncertainty
should not be used to compensate for a deliberately skewed duty cycle.

## When to *increase* uncertainty (not as decoration)

Increase uncertainty as a *temporary* safety net only when:

- A known PLL spec changes mid-project (vendor update, characterization
  delay) — bump uncertainty until the new value is signed off.
- Pre-silicon margin against an OCV/AOCV model you don't fully trust.
- Inserting a guard band for crosstalk you haven't yet enabled in STA.

In all cases, log the rationale. "Uncertainty 250 ps because" should be
findable in the SDC comments — otherwise it ossifies and over-margins
every future closure.

## Reporting

```tcl
report_clock_properties        ;# shows uncertainty on each clock
report_timing -path_type full_clock  ;# 'clock uncertainty' line is explicit
```

Look for the line `clock uncertainty -X.XXX` in the data-required block.
That is the value subtracted from your available period.

## Common mistakes

- **Forgetting to reduce uncertainty after `set_propagated_clock`.** Leaves
  pre-CTS skew estimate stacked on top of real skew → over-pessimism →
  unnecessary buffer insertion.
- **Hold uncertainty = setup uncertainty.** Hold is usually smaller; using
  setup value for hold over-margins and can force hold buffers where none
  needed.
- **Setting per-path uncertainty for normal flop2flop paths.** Use
  per-clock-pair (which scales) instead of per-path (which doesn't).
- **Treating uncertainty as a slush fund.** Adding 50 ps "for safety" on
  every closure makes 200 ps of bogus pessimism within a year.

## See also

- `setup-hold-equations.md` — where uncertainty plugs into the slack
  formula.
- `ocv-aocv-pocv.md` — derating is the *other* knob; do not double-count.
- `report-timing-deepdive.md` — finding uncertainty in the report.
