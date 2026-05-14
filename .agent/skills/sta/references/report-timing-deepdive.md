# report_timing — Field-by-Field Deep Dive

> Reading a real `report_timing -path_type full_clock_expanded` output.
> What every field means and which equation term it maps to.

## The canonical report

```
Startpoint: u_alu/op_reg_q_reg[5]
            (rising edge-triggered flip-flop clocked by clk_core)
Endpoint:   u_alu/result_reg_q_reg[5]
            (rising edge-triggered flip-flop clocked by clk_core)
Path Group: clk_core
Path Type:  max  (setup)
Corner:     ss_0p81v_125c

  Point                                       Incr     Path
  ----------------------------------------------------------------
  clock clk_core (rise edge)                  0.000    0.000
  clock network delay (propagated)            0.130    0.130     ← T_launch_clk_arrival
  u_alu/op_reg_q_reg[5]/CK (DFFRX1)           0.000    0.130
  u_alu/op_reg_q_reg[5]/Q  (DFFRX1)           0.105    0.235     ← T_cq
  u_alu/add_inst/sum[5]    (ADDF_X1)          0.182    0.417
  u_alu/and_inst/Y         (AND2_X1)          0.094    0.511
  u_alu/buf_inst/Y         (BUF_X2)           0.071    0.582
  u_alu/result_reg_q_reg[5]/D (DFFRX1)        0.180    0.762     ← T_logic
  data arrival time                                    0.762

  clock clk_core (rise edge)                  1.000    1.000     ← T_period
  clock network delay (propagated)            0.140    1.140     ← T_capture_clk_arrival
  clock reconvergence pessimism               0.012    1.152     ← T_CRPR_credit
  u_alu/result_reg_q_reg[5]/CK (DFFRX1)       0.000    1.152
  library setup time                         -0.050    1.102     ← T_setup
  clock uncertainty                          -0.080    1.022     ← T_uncertainty
  data required time                                   1.022

  data required time                                   1.022
  data arrival time                                   -0.762
  ----------------------------------------------------------------
  slack (MET)                                          0.260
```

## Field map

| Report field | Equation term | Source |
|---|---|---|
| Startpoint | launch register / port | netlist |
| Endpoint | capture register / port | netlist |
| Path Group | which group (in→reg, reg→reg, etc.) | tool-derived |
| Path Type | `max` = setup, `min` = hold | report flags |
| Corner | which MMMC view | `set_analysis_view` |
| clock network delay | T_launch_clk_arrival / T_capture_clk_arrival | clock tree |
| /CK arrival | 0 by convention | reference point |
| /Q delay | T_cq | `.lib` cell timing |
| cell/net delays | T_logic (sum) | `.lib` + parasitics |
| /D arrival | T_cq + T_logic | accumulated |
| data arrival time | T_launch + T_cq + T_logic | sum |
| clock period | T_period | `create_clock -period` |
| clock reconvergence pessimism | T_CRPR_credit | CRPR engine |
| library setup time | T_setup | `.lib` |
| clock uncertainty | T_uncertainty | `set_clock_uncertainty` |
| data required time | T_capture + T_period + T_CRPR − T_setup − T_uncertainty | computed |
| slack | required − arrival | computed |

## Hold report

Hold uses **min** delays and **same edge** at launch and capture:

```
  Point                                       Incr     Path
  ----------------------------------------------------------------
  clock clk_core (rise edge)                  0.000    0.000
  clock network delay (propagated)            0.110    0.110     ← min path
  u_alu/op_reg_q_reg[5]/Q  (DFFRX1)           0.075    0.185     ← T_cq_min
  u_alu/add_inst/sum[5]    (ADDF_X1)          0.135    0.320
  u_alu/result_reg_q_reg[5]/D (DFFRX1)        0.140    0.460
  data arrival time                                    0.460

  clock clk_core (rise edge)                  0.000    0.000
  clock network delay (propagated)            0.140    0.140     ← max path
  clock reconvergence pessimism              -0.012    0.128
  library hold time                           0.020    0.148     ← T_hold
  clock uncertainty                           0.030    0.178     ← uncertainty (hold)
  data required time                                   0.178

  data arrival time                                    0.460
  data required time                                  -0.178
  ----------------------------------------------------------------
  slack (MET)                                          0.282
```

Note: CRPR sign flipped (helps hold instead of hurting it), uncertainty
is *added* (tightens the window), period is absent (same-edge).

## Path types — what each shows

| `-path_type` | Use case |
|---|---|
| `short` (default) | One-line summary per path; triage only |
| `full` | Full data path; for fix decisions |
| `full_clock` | Adds clock-network arrival at both CKs |
| `full_clock_expanded` | Expands clock tree into individual buffers |

For master-level debugging: **always** `full_clock_expanded`. You need to
see which buffer in the clock tree is contributing skew.

## Useful options

```tcl
# Show derate column
report_timing -derate

# Show SI delta-delay columns
report_timing -crosstalk_delta

# PBA (path-based analysis) for tight signoff
report_timing -pba_mode path

# Worst N paths per endpoint
report_timing -nworst 10 -max_paths 50

# Slack threshold
report_timing -slack_lesser_than 0.05

# Through-cell filter (for triage)
report_timing -through u_alu/add_inst/Y

# Path group filter
report_timing -group {clk_core REG2REG}

# Min and max in one run
report_timing -delay_type min_max

# Export for diff
report_timing -file timing.rpt
```

## Where pessimism hides

In a real report, search for these anomalies:

| Anomaly | Meaning |
|---|---|
| `clock network delay (ideal)` instead of `(propagated)` | `set_propagated_clock` missing — pre-CTS view masquerading as post-CTS |
| Missing CRPR line | CRPR disabled — slack pessimistic by 10–30 ps typical |
| Derate column shows 1.000 everywhere | Derate not loaded; signoff unsafe at 28 nm+ |
| Uncertainty same as pre-CTS post-CTS | Forgot to reduce uncertainty after `set_propagated_clock` |
| CRPR credit > clock latency | CRPR computation bug or wrong common-portion identification |
| No `Δ_delay` columns with SI on | SI not engaged on this view |
| Setup at FF corner | Wrong corner — setup should be SS |
| Hold at SS corner | Wrong corner — hold should be FF |

## Triaging from the report

1. **Look at path group.** If reg2reg, fix is internal. If in/out, fix is
   often an I/O budget bug.

2. **Sum the logic delay vs `T_cq + T_setup`.** If logic >> sum, RTL is
   the bottleneck. If logic < `T_cq + T_setup` and you're still failing,
   the constraint is wrong.

3. **Check the clock arrival difference.** Big skew = clock-tree issue,
   not logic.

4. **Verify CRPR credit and derate.** Disable CRPR with `-crpr_threshold
   inf` to see the un-credited slack. If un-credited slack is healthy,
   you have pessimism, not a real violation.

5. **Cross-corner.** If only one MMMC view fails, the fix may be
   corner-specific (different cell sizing, library tweak).

## Cross-correlation with synthesis

A path that looks long in `report_timing` may be a synthesis artifact:

- **Unbalanced muxing** — synthesis chose a deep mux tree instead of a
  carry chain. Force `keep_hierarchy` or rewrite RTL.
- **Latches inferred** — incomplete `always_comb`; see `latch-timing.md`.
- **Failed retiming** — synthesis didn't pipeline because of a `dont_touch`
  attribute or an async-clear ambiguity.

When in doubt, dump the synthesized netlist for the failing path and
read it. The report names map to net/cell names in the netlist.

## See also

- `setup-hold-equations.md` — what the math should be.
- `crpr.md` — interpreting the CRPR line.
- `ocv-aocv-pocv.md` — derate columns.
- `si-crosstalk.md` — delta columns.
- `mmmc-corners.md` — per-view reports.
