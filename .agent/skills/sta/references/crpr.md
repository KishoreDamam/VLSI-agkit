# CRPR — Clock Reconvergence Pessimism Removal

> Why STA adds pessimism the silicon doesn't have, and how CRPR credits it
> back. When to enable, when it lies, and how to verify the credit.

## The pessimism problem

Setup analysis uses **late** clock arrival at capture and **early** clock
arrival at launch (worst case). Hold analysis uses **early** capture and
**late** launch (also worst case).

But a real chip has *one* clock tree. The buffers in the **common
portion** of the clock path (the segment shared by launch and capture)
cannot simultaneously be "fast for launch and slow for capture" — they
are the *same physical buffers* on the *same die at the same instant*.

Without CRPR, the STA engine double-counts variation on the common path:
once toward launch (early), once toward capture (late). The result is
pessimism that doesn't exist on silicon.

```
Clock root
  |
  +-- B1 ---+--- B2 ---> launch_reg CK   (path A)
            |
            +--- B3 ---> capture_reg CK  (path B)

Common portion = root → B1
```

The buffer B1 is on both paths. CRPR credits back the pessimism applied
to B1.

## How CRPR computes credit

For each path, the tool:

1. Identifies the **common clock-path segment** (root → last shared cell).
2. Computes the **maximum derate difference** applied across that segment.
3. Subtracts that difference from the slack (adds it as credit).

For **flat OCV**:

```
T_CRPR_credit = T_common * (derate_late - derate_early)
              = 100 ps * (1.05 - 0.95)
              = 10 ps
```

For **AOCV**, the credit is computed per-stage with depth-dependent
factors, summed linearly.

For **POCV**, the credit is RSS of the per-stage sigmas on the common
path — typically smaller than AOCV credit but statistically accurate.

## Enabling CRPR

```tcl
# PrimeTime (default on with timing_remove_clock_reconvergence_pessimism true)
set timing_remove_clock_reconvergence_pessimism true

# Tempus (default on)
set_analysis_view -setup ...                  ;# CRPR active in MMMC
report_crpr -from launch_reg -to capture_reg  ;# inspect credit

# Vivado: CRPR always on for synchronous clocks, no toggle
```

## Verifying CRPR actually applied

`report_timing -crpr_threshold 0.0` will print the CRPR credit line:

```
  clock network delay (propagated)    0.130
  clock uncertainty                  -0.080
  clock reconvergence pessimism       0.015     <-- CRPR credit
  data required time                  1.065
```

If the line is missing on a multi-buffer clock tree, CRPR is disabled or
the engine is treating the clocks as having no common ancestor (often a
generated-clock declaration issue — see `timing-constraints`).

## When CRPR is small or zero

- **Generated clocks with `-add` clauses** that decouple the source —
  may share no common buffer in STA's model.
- **`set_clock_groups -asynchronous`** — paths between async clocks have
  no shared analysis; CRPR is meaningless.
- **Different clock roots** — two independent PLLs feeding different
  domains; expect zero common portion.
- **Mux'd clocks (`-case_analysis` driven)** — common portion depends on
  which input is selected. Some tools over-credit here; audit with
  `report_crpr`.

## When CRPR lies (over-credits)

- **Inverter pairs not modeled as common.** If launch and capture take
  different polarities through the same buffer, the tool may treat them
  as separate cells. Library characterization issue.
- **Custom CTS that splits trees aggressively.** Some hierarchical CTS
  flows create logically common but physically separate trees; engine
  may credit pessimism that silicon doesn't share.
- **Clock-gating cells in the common portion.** The gate's enable
  arrival may differ between paths; over-crediting is possible if the
  enable arc is symmetric in the library but asymmetric in placement.

If your design fails silicon despite signoff WNS > 0, double-check
`report_crpr` for over-credit on the critical path.

## CRPR credit ≠ free margin

A frequent mistake at design review:

> "WNS was −20 ps, but CRPR adds 30 ps so we're +10 ps — ship it."

CRPR is removing **fake** pessimism the STA tool added. Without CRPR,
your tool was lying about the design being worse than it is. *With* CRPR,
your design has *zero* real margin against the corner you're closing.

Closing on CRPR credit means:

- Any tightening of OCV/AOCV/POCV will erase the credit.
- Any change to clock tree topology that reduces common portion will
  erase the credit.
- Foundry deck updates can disable CRPR (rare, but happens) and erase
  the credit.

Treat CRPR-dependent closure as a yellow flag, not a green light.

## CRPR across modes / corners

In MMMC, each view has its own CRPR setting. Common mistake: enable CRPR
in `setup_typical` but forget in `setup_slow_slow`. The slow-slow signoff
report shows artificial pessimism and the design "fails" timing that it
actually meets.

Audit:

```tcl
foreach view [all_analysis_views] {
  set_analysis_view -setup [get_views $view]
  puts "$view: [get_app_var timing_remove_clock_reconvergence_pessimism]"
}
```

## CRPR and useful skew

Useful skew (`set_clock_latency` hints to CTS) deliberately shifts clock
arrival on one register. The shifted register's clock path no longer
fully shares the common portion → CRPR credit shrinks on paths through it.
Sometimes this *eliminates* the useful-skew benefit. Verify with
`report_timing -path_type full_clock_expanded` before and after.

## Reporting

```tcl
report_crpr -from launch_reg -to capture_reg
report_timing -crpr_threshold 0.0 -path_type full_clock
get_attribute [get_timing_paths -from launch_reg -to capture_reg] crpr
```

## Common mistakes

- **Disabling CRPR on hold.** Hold check has its own CRPR (early launch
  / late capture orientation). Disabling adds spurious hold pessimism →
  unnecessary buffer insertion.
- **CRPR on with no derate.** With derate=1.0 there is no pessimism to
  remove; CRPR credit will be zero. Not a bug, but verify derate is
  loaded if you expected credit.
- **CRPR credit too large at 16 nm.** With POCV the credit should be
  small (RSS, not sum). If the credit is huge, POCV mode is off and
  CRPR is using flat-OCV math — check `pocv_enable`.
- **Generated clocks without `-master_clock`.** Engine may not identify
  common portion correctly; check `report_clocks -hierarchy`.

## See also

- `ocv-aocv-pocv.md` — CRPR credit is per-derate-model.
- `setup-hold-equations.md` — `T_CRPR_credit` term placement.
- `mmmc-corners.md` — CRPR per view.
