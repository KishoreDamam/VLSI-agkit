# OCV / AOCV / POCV — Derating Models

> Flat OCV, Advanced OCV, and Parametric/Statistical OCV. Which model is
> mandatory at which node, and the math behind each.

## Why derating exists

Two identical cells, placed adjacent on the same die, have different
delays. Sources of variation:

- **Random variation (Vth mismatch, channel-length variation)** — varies
  per-cell, uncorrelated.
- **Systematic variation (Vdd droop, temperature gradient, density)** —
  varies across the die, spatially correlated.
- **Litho / etch variation** — depends on neighborhood, layer.

STA derating multiplies cell delays by a factor (>1 for setup, <1 for
hold) to bound the worst-case scenario per path.

## Model 1: Flat OCV

The simplest model. One number for setup, one for hold:

```tcl
set_timing_derate -early -cell_delay 0.95   ;# fast cells 5% faster
set_timing_derate -late  -cell_delay 1.05   ;# slow cells 5% slower
set_timing_derate -early -net_delay  0.95
set_timing_derate -late  -net_delay  1.05
```

**Pros:** trivial to enable; works on any tool.

**Cons:** the same 5% pessimism on a 50-cell path that on a 5-cell path —
which is wrong, because random variation averages out over depth.

**Node fit:** ≥ 90 nm. At 28 nm+ flat OCV is either too pessimistic
(killing closure) or too optimistic (failing silicon). Foundry decks
forbid flat OCV at these nodes.

## Model 2: AOCV (Advanced OCV)

Derate depends on **path depth** (number of stages) and **distance**
(physical extent). Deeper paths get less pessimism because random
variation averages out.

AOCV tables are 2-D (depth × distance) per cell type, supplied by the
library vendor:

```
  depth →   1    2    4    8    16   32
  dist↓
  100 µm  1.10 1.07 1.05 1.04 1.03 1.025
  500 µm  1.12 1.09 1.06 1.05 1.04 1.03
  1000 µm 1.13 1.10 1.07 1.06 1.05 1.04
```

Enable:

```tcl
read_aocv_table aocv_corner.txt
set_timing_derate -aocv [list ...]      ;# tool-specific syntax
analyze_aocv -path mode_aocv            ;# Cadence Tempus
```

**Pros:** removes ~50% of flat-OCV pessimism on deep paths.

**Cons:** requires foundry-supplied AOCV tables; doesn't model
cell-level distribution sigma (treats variation as bounded).

**Node fit:** 28–65 nm. Mandatory for signoff at these nodes.

## Model 3: POCV / SOCV (Parametric / Statistical OCV)

Each cell has a **per-stage sigma** (σ_cell) characterized by the
library. STA computes path-level variation as the RSS (root-sum-square)
of cell sigmas, treating each as independent random Gaussian:

```
σ_path = sqrt( σ_cell_1² + σ_cell_2² + ... + σ_cell_N² )

Effective derate = mean + k * σ_path
                  where k = 3 (3-sigma) or 4.5 (per foundry spec)
```

Enable:

```tcl
set_app_var timing_pocvm_enable_analysis true        ;# PrimeTime
read_pocvm_table  pocv_corner.pocvm
analyze_pocv -path mode_pocv                          ;# Tempus
```

**Pros:**

- Tracks node-level random variation accurately.
- Less pessimistic than AOCV on long paths (RSS instead of linear sum).
- Captures correlation effects (e.g., adjacent cells share Vth).

**Cons:**

- Library characterization data heavy.
- Tool flow more complex (LVF, OCV tables, AOCV tables, POCV tables).

**Node fit:** ≤ 16 nm. Foundry-mandated for signoff. At 7 nm and below,
**LVF (Liberty Variation Format)** extends POCV with moment-based modeling
of slew/load dependence.

## Per-corner derate is *not* OCV/AOCV/POCV

`set_timing_derate -early 0.9 -late 1.1` on a single corner is **flat
OCV**, regardless of how aggressive the number is. AOCV requires reading
foundry depth tables; POCV requires reading per-cell sigma. If you can't
point to a foundry deck file you read, you have flat OCV.

## When each model applies in the flow

| Phase | Setup model | Hold model |
|---|---|---|
| Synth | Flat OCV (typ ±5%) | Flat OCV (typ ±2%) |
| Pre-CTS placement | AOCV (typical foundry mid-corner) | Flat OCV ok |
| Post-CTS | AOCV or POCV per foundry | AOCV or POCV |
| Sign-off | POCV (≤ 16 nm) / AOCV (28–65 nm) | Same |
| ECO | Same as signoff view used for ECO target | Same |

## Derate and CRPR interaction

CRPR (Clock Reconvergence Pessimism Removal) credits back the derate that
applied **identically** to the common portion of the launch and capture
clock paths. With OCV, the engine subtracts identical multipliers from
the common segment.

With AOCV/POCV, CRPR is **per-stage**: the engine identifies each common
buffer and credits the per-stage variance. POCV CRPR is RSS-based, so the
credit is small but exact.

Disabling CRPR with AOCV/POCV produces 200–500 ps of pessimism on
deep clock trees. Always enable CRPR alongside AOCV/POCV. See `crpr.md`.

## Common pitfalls

- **Flat OCV at 16 nm "to be safe".** Foundry deck will fail signoff
  review; flat OCV at advanced nodes is either too tight (kills WNS)
  or too loose (misses silicon failures depending on cell mix).
- **AOCV without distance dimension.** Some flows skip the distance
  axis; this under-models long, sparsely connected clock trees.
- **POCV tables loaded but `pocv_enable` flag false.** Tool falls back
  silently to flat OCV; check `report_timing` derate field.
- **Mixing AOCV and POCV on different paths.** Engine reports become
  inconsistent — pick one mode per signoff run.
- **CRPR disabled with AOCV.** Adds spurious pessimism; common in legacy
  scripts copied from pre-AOCV nodes.

## Reporting derate

```tcl
report_timing -derate                  ;# shows derate per cell in the path
report_aocv_path_analysis -slack_lesser_than 0.1   ;# Tempus
get_timing_derate -from <cell>         ;# query active derate
```

In the report, look for the `Derate` column next to each cell delay.
If absent, derate is not applied (or report is using `-path_type short`).

## See also

- `crpr.md` — pessimism removal that pairs with OCV/AOCV/POCV.
- `mmmc-corners.md` — derate is set per corner; multi-corner runs use
  different derate per view.
- `setup-hold-equations.md` — where derate plugs into the slack formula.
