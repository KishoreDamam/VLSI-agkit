# MMMC — Multi-Mode Multi-Corner

> Sign-off requires closing at multiple PVT/RC corners and operating modes.
> Picking the right corner for setup vs hold, and not over-signing.

## What MMMC means

| Axis | What it varies | Examples |
|---|---|---|
| **Mode** | Functional operating state | Functional, Test (scan), DFT, low-power |
| **Process corner** | Device characteristics | TT (typical), SS (slow-slow), FF (fast-fast), SF, FS |
| **Voltage** | Supply voltage | 0.81 V (nominal − 10%), 0.9 V (nom), 0.99 V (nom + 10%) |
| **Temperature** | Junction temperature | 125 °C (hot), 25 °C (room), −40 °C (cold) |
| **RC corner** | Interconnect parasitics | C-best/R-worst, C-worst/R-best, typical |

A **view** = (mode, corner) tuple. MMMC sign-off runs N modes × M corners
simultaneously, reporting WNS/TNS per view.

## Setup vs hold corner — they are different

Setup analysis wants **worst-case delay** (data is slow, can't reach D in
time). Hold wants **best-case delay** (data is fast, races past the
capture clock).

| Check | Process | Voltage | Temperature | RC |
|---|---|---|---|---|
| **Setup** | SS (slow-slow) | low (0.81 V) | hot (125 °C) | C-worst / R-worst |
| **Hold**  | FF (fast-fast) | high (0.99 V) | cold (−40 °C) | C-best / R-best |

**Both** corners must be signed off — a single "worst case" corner
doesn't exist. Hold violations at FF/0.99V/−40 are real silicon failures
even if SS/0.81/125 closes setup perfectly.

## Why temperature inverts at advanced nodes

At 90 nm+, transistors are faster at low T (low ⇒ fast). Hold worst case
is therefore cold.

At ≤ 28 nm, **temperature inversion** appears: at low Vdd, transistors
can be *faster* at higher temperature (mobility effects swamp Vth shift).
The "fast" corner for hold may be hot, not cold. Always check the foundry
deck for the corner combinations to sign off.

## Sign-off views — minimum set

| View | Mode | Corner | Check |
|---|---|---|---|
| `func_setup_ss_low_hot_rc_worst` | functional | SS / 0.81 / 125 / Cw-Rw | setup |
| `func_hold_ff_high_cold_rc_best` | functional | FF / 0.99 / −40 / Cb-Rb | hold |
| `scan_setup_ss_low_hot_rc_worst` | scan | SS / 0.81 / 125 / Cw-Rw | setup |
| `scan_hold_ff_high_cold_rc_best`  | scan | FF / 0.99 / −40 / Cb-Rb | hold |

Typical signoff has 8–16 views; advanced nodes (7 nm) push to 30+. The
foundry deck specifies the exact list.

## Setting up MMMC (Tempus / Innovus / PrimeTime)

```tcl
# Innovus / Tempus
create_library_set -name LIB_SS -timing $LIB_SS_FILES
create_library_set -name LIB_FF -timing $LIB_FF_FILES
create_library_set -name LIB_TT -timing $LIB_TT_FILES

create_rc_corner   -name RC_W   -cap_table $CAP_W -T 125
create_rc_corner   -name RC_B   -cap_table $CAP_B -T -40

create_delay_corner -name DC_SS_W -library_set LIB_SS -rc_corner RC_W
create_delay_corner -name DC_FF_B -library_set LIB_FF -rc_corner RC_B

create_constraint_mode -name FUNC -sdc_files $SDC_FUNC
create_constraint_mode -name SCAN -sdc_files $SDC_SCAN

create_analysis_view -name FUNC_SETUP_SS -constraint_mode FUNC -delay_corner DC_SS_W
create_analysis_view -name FUNC_HOLD_FF  -constraint_mode FUNC -delay_corner DC_FF_B

set_analysis_view -setup {FUNC_SETUP_SS SCAN_SETUP_SS} \
                  -hold  {FUNC_HOLD_FF  SCAN_HOLD_FF}
```

```tcl
# PrimeTime — DMSA (Distributed Multi-Scenario Analysis)
create_scenario -name FUNC_SETUP_SS -common $COMMON -specific $SPEC_FUNC_SETUP_SS
create_scenario -name FUNC_HOLD_FF  -common $COMMON -specific $SPEC_FUNC_HOLD_FF
set_active_scenarios *
```

## RC corners — easy to get wrong

`C-best / R-best` ≠ `min`. The combinations matter:

| RC corner | What it models | Hurts |
|---|---|---|
| **C-worst, R-worst** | Tight metal, high cap, high R | Setup (slow nets) |
| **C-best, R-best** | Loose metal, low cap, low R | Hold (fast nets) |
| **C-worst, R-best** | High cap, low R — capacitive nets | Setup on long nets |
| **C-best, R-worst** | Low cap, high R — resistive nets | Hold on short nets, RC delay |

Foundry decks may specify all four for advanced nodes. Mid-range (28 nm)
often uses just Cw-Rw and Cb-Rb.

## Mode-specific differences

Modes change *constraints*, not corners. Common modes:

- **Functional** — normal operation; clock from PLL.
- **Scan-shift** — scan clock (slower) drives all flops; data through
  scan chain. Setup deadlines are relaxed (slow shift clock); hold is
  still tight because shift races.
- **Scan-capture** — functional clock, but scan-enable=0 and chain in
  capture mode. Same setup as functional.
- **DFT BIST** — built-in test mode; memory paths excluded from STA.
- **Sleep / retention** — only retention flops clocked; most paths
  excluded via `set_case_analysis`.

Each mode has its own SDC. Use `set_case_analysis` to fix mode-select
signals so the engine analyzes the right paths.

## Over-signoff is real cost

Adding views beyond the foundry list:

- **Doubles runtime** per added scenario.
- **Adds ECO cycles** — fixing a marginal view that silicon never sees.
- **Distorts timing budget** — over-margining one view tightens others.

The signoff matrix is calibrated against silicon characterization. Trust
the deck; don't add views "for safety".

## Sign-off acceptance

Each view must independently pass:

- **WNS** ≥ 0 ps (or per foundry target margin, typically ≥ +10 ps)
- **TNS** ≥ 0
- **WHS** ≥ 0
- **THS** ≥ 0
- `report_min_pulse_width` clean
- `report_clock_skew` within budget

Some flows accept slightly negative WNS on a "non-critical" view if the
governing view is positive — this is dangerous and should be a flagged
exception, not a default.

## Common pitfalls

- **One SDC for all modes.** Different modes need different
  `set_case_analysis` and different I/O constraints. Forcing one SDC
  results in unconstrained paths in some modes.
- **Setup signed off only at SS, hold only at FF.** Standard, but
  remember **mode** also matters — sign off setup *and* hold in *each*
  mode.
- **Skipping RC corners.** "Typical RC" is not a signoff corner. Net
  delay variation can swing slack by 20% at 16 nm.
- **Ignoring temperature inversion.** Hold at hot Vmin can fail at
  advanced nodes; foundry deck calls this out — read it.
- **Reusing pre-CTS uncertainty post-CTS across views.** Each view's
  uncertainty must be updated after CTS for that view's clock tree.

## Reporting MMMC

```tcl
report_analysis_views                       ;# all active views
report_timing_summary -views {view1 view2}  ;# per-view summary
report_timing -views all -unique_pins       ;# worst path across views
```

## See also

- `ocv-aocv-pocv.md` — derate is per-corner; signoff matrix multiplies.
- `clock-uncertainty.md` — uncertainty is per-view.
- `report-timing-deepdive.md` — reading per-view reports.
