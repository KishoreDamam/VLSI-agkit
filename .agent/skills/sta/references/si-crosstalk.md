# Signal Integrity & Crosstalk in STA

> Aggressor/victim coupling, delta-delay, glitch propagation, noise on
> clocks. Enabling SI-aware STA and interpreting the results.

## Why SI matters in STA

Without SI, STA computes each net's delay independently from its driver,
load, and parasitics. With SI, neighbor nets switching simultaneously
**couple** capacitively through interconnect; the victim's delay shifts
(±delta-delay) and may glitch.

At 90 nm SI added 5–10% to critical-path delay. At 7 nm it can add
30–40% if the design ignores coupling — SI-aware STA is mandatory.

## Aggressor and victim

```
        ───────┐  ┌──────  victim (slow signal of interest)
               │  │
        ═══════╪══╪══════  coupled segment (parasitic Cc)
               │  │
        ───────┘  └──────  aggressor (neighbor switching)
```

- **Aggressor** — net that switches while the victim is transitioning.
- **Victim** — net under analysis.
- **Coupling capacitance Cc** — parasitic capacitance between adjacent
  nets, extracted by the parasitic-extraction (PEX) tool.

The aggressor's transition imparts a coupled current into the victim,
either *helping* (same direction) or *opposing* (opposite direction)
the victim's transition.

## Delta-delay

Net-by-net delay shift caused by coupling:

```
Δ_delay = Cc * (1 - aggressor_switching_alignment) * (V_swing / I_drive)
```

For setup analysis: **worst aggressor opposes victim** (slows it).
For hold analysis: **best aggressor aids victim** (speeds it up).

Both must be enabled — they affect setup and hold opposite ways.

## Glitch / noise

Even on a *static* victim, a switching aggressor can inject enough
charge to cause the victim to **glitch** above the receiver threshold.

```
Aggressor:  __|‾‾‾‾‾|__
Victim:     _________________  (should be quiet)
Actual:     _____/‾\___________  (glitch from coupling)
```

If the victim is a clock or async preset, the glitch propagates as a
spurious edge. STA noise analysis (`report_noise`) flags such cases.

## Enabling SI

```tcl
# PrimeTime SI
set timing_save_pin_arrival_and_slack true
set si_analysis_logical_correlation_mode true
update_timing -full

# Tempus
set_analysis_view -setup [list ...]
set_db delaycal_enable_si true
set_db delaycal_input_transition_delay 0
update_delay -si

# Innovus
setDesignMode -process 16 -node "16nm"
setSIMode -analysisType bestWorst
timeDesign -si -postRoute
```

After enabling, `report_timing` shows two delay numbers per cell: nominal
and delta. The slack equation has an extra term:

```
Setup slack = ... - sum(Δ_delay_late_aggressors)
Hold  slack = ... + sum(Δ_delay_early_aggressors)
```

## Filtering aggressors

Not every net is a meaningful aggressor. Tools filter by:

- **Logical correlation** — if aggressor and victim are driven by the
  same logic cone and never switch simultaneously, exclude. (Requires
  symbolic analysis; expensive but reduces pessimism.)
- **Sensitization window** — if aggressor's transition window is
  outside the victim's transition window, exclude.
- **Voltage threshold** — if Cc * Vdd / Cload < threshold, exclude.

Without filtering, SI runtime explodes and pessimism balloons. Foundry
decks specify thresholds; respect them.

## Noise on clocks

Clock nets are special: a glitch on a clock can cause spurious capture
or skip an edge. Tools have dedicated checks:

```tcl
report_noise -above_low -above_high -clocks
```

If any clock net shows noise > 0.3 × Vdd (typical), re-route with:

- Shielding (Vss tracks on both sides of clock).
- Wider spacing to adjacent signals.
- Different metal layer (lower coupling).

Most CTS tools apply clock shielding by default; verify with
`report_routing -nets <clk_net>`.

## SI in MMMC

SI must be enabled **per view**. Some flows enable SI only on signoff
views; pre-CTS views skip SI for speed. After CTS, SI must be on for
every signoff view — otherwise post-route closure surprise.

A frequent miss: SI enabled for setup, disabled for hold. Both directions
need SI — hold races are *worse* with SI because best-case aggressors
*speed up* the victim.

## Reporting and triage

```tcl
report_si_bottleneck -cost_type delay -nworst 20
# Lists nets with largest delta-delay contribution.

report_timing -path_type full_clock_expanded -derate -crosstalk_delta
# 'CK Delta' and 'Data Delta' columns show coupling impact.
```

Typical delta-delay budget:

| Net type | Acceptable delta |
|---|---|
| Critical data | < 5% of nominal cell delay |
| Clock | < 2% of period |
| Async preset/clear | Noise margin > 0.3 × Vdd |

Above these, take action: shielding, spacing, repeater insertion, or
re-routing.

## Common pitfalls

- **PEX without coupling.** RC-only extraction omits Cc; SI becomes
  meaningless. Use Cc+RC extraction (`startCcOpt` or PEX coupling mode).
- **SI on, but logical correlation off.** Runtime explodes, results
  over-pessimistic. Enable correlation for signoff.
- **Skipping SI on hold.** Best-aggressor speed-ups cause hold failures;
  must enable both.
- **No clock shielding.** Pre-route flows often skip; verify post-route
  that clock nets have shield tracks.
- **Aggressor list ignores power nets.** At advanced nodes Vdd/Vss can
  couple to adjacent signals — include power nets if PEX provides them.

## Sign-off acceptance

- WNS / WHS within target *with SI enabled*.
- `report_noise` clean on all clocks and async pins.
- Top-20 SI bottlenecks within delta-delay budget.
- Foundry-mandated SI-mode flags set (varies per node).

## See also

- `ocv-aocv-pocv.md` — SI delta-delay is **additive** to OCV derate.
- `mmmc-corners.md` — SI per view; both Cw-Rw and Cb-Rb extract coupling.
- `report-timing-deepdive.md` — delta columns in the report.
