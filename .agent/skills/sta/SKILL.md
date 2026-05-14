---
name: sta
description: Use for Static Timing Analysis — interpreting setup/hold slack, reading report_timing, clock uncertainty budgets, OCV/AOCV/POCV derating, CRPR, latch time-borrowing, MMMC sign-off corners, SI/crosstalk-aware timing, and closing setup/hold violations.
---

# Static Timing Analysis (STA)

> Master-level STA: how to read a timing report, where slack comes from, and how
> to close violations on a real signoff flow. Constraint *authoring* lives in
> `timing-constraints`; this skill is about *analysis* and *closure*.

## When to use

- A timing report shows WNS < 0 or WHS < 0 and you need to triage and fix.
- Reading `report_timing` and need to understand every field (launch clock,
  capture clock, CRPR credit, derate, uncertainty).
- Sign-off across MMMC corners and need to pick the right view for setup vs hold.
- Deciding between OCV / AOCV / POCV for a process node.
- Designing with latches and computing time-borrow budgets.
- SI/crosstalk has been enabled and delta-delays are eating margin.
- Auditing whether your clock uncertainty budget is realistic vs PLL+SSC+jitter.
- Comparing slack between two synthesis runs — which corner moved, and why.

**Not for:** authoring SDC (use `timing-constraints`), CDC structural checks
(`clock-domain-crossing`), or floorplan/CTS fixes (`physical-design` if
present, otherwise tool-flow skills).

## Pre-requisites

- **Inputs:** timing report (`report_timing`, `report_timing_summary`),
  the SDC used to produce it, library `.lib` corner names, and netlist.
- **Tool versions:** any SDC 1.9+ STA engine (PrimeTime, Tempus, Vivado).
- **Prior skills:** `timing-constraints` (so you can read what the SDC says);
  `synthesis-guidelines` (so you know what optimizations were already tried).

## The slack equation (memorize this)

For a single register-to-register path:

```
Setup slack = T_capture_clk_arrival - T_launch_clk_arrival - T_cq - T_logic
              - T_setup - T_uncertainty + T_CRPR_credit
            = (T_period + T_skew - T_uncertainty)
              - (T_cq + T_logic + T_setup) + T_CRPR_credit

Hold slack  = T_launch_clk_arrival + T_cq + T_logic
              - T_capture_clk_arrival - T_hold - T_uncertainty + T_CRPR_credit
```

Every field in `report_timing` maps to one of these terms. See
`references/setup-hold-equations.md` for the full derivation with numbers.

## Procedure — closing a violation

1. **Classify the path.** `report_timing` header tells you the path group
   (in→reg, reg→reg, reg→out, in→out). Different groups have different fix
   tiers. See `references/timing-paths.md`.

2. **Read the report end-to-end.** Confirm: launch clock period, capture clock
   period, skew, uncertainty, CRPR credit, derate factor, and which corner.
   See `references/report-timing-deepdive.md`.

3. **Decide if the constraint is honest.** Most violations are constraint
   bugs, not logic bugs. Walk through `references/setup-hold-equations.md`
   §"sanity checklist" before touching RTL.

4. **Pick the cheapest fix that doesn't lie.** Fix tiers, cheapest first:

   ```dot
   digraph fix {
       rankdir=TB;
       "WNS < 0" -> "Constraint wrong?";
       "Constraint wrong?" -> "Fix SDC (multicycle/false/groups)" [label="yes"];
       "Constraint wrong?" -> "Useful skew available?" [label="no"];
       "Useful skew available?" -> "set_clock_latency / CTS hint" [label="yes"];
       "Useful skew available?" -> "Logic restructure (retiming, factoring)" [label="no"];
       "Logic restructure (retiming, factoring)" -> "RTL pipelining";
   }
   ```

5. **Re-run and compare.** Look at `report_timing -delay min_max -path full_clock_expanded`
   diff before/after. Confirm you didn't push the violation onto a different
   path or corner.

6. **Sign off across MMMC.** Setup at slow-slow, hold at fast-fast, SI
   enabled, and an OCV/AOCV/POCV view that matches the foundry deck.
   See `references/mmmc-corners.md`.

## Validation gates

- **Gate 1:** `check_timing` — zero unconstrained endpoints, zero missing
  generated clocks, zero loops.
- **Gate 2:** `report_clocks` — every clock has a period and a source.
- **Gate 3:** `report_timing_summary` — WNS ≥ 0 and WHS ≥ 0 on every
  signoff view (not just the typical corner).
- **Gate 4:** `report_min_pulse_width` and `report_clock_skew` — neither
  reports violations on critical clock nets.
- **Gate 5:** With SI on, delta-delays for top-N critical nets are within
  the noise budget defined in `references/si-crosstalk.md`.
- **Gate 6:** OCV/AOCV/POCV mode matches what the foundry sign-off deck
  prescribes for the node (28nm+ should not use flat OCV).

## Common failure modes & recovery

| Symptom | Likely cause | Fix |
|---|---|---|
| Setup violation gone after `set_false_path` but design still fails on silicon | False path masked a real reg2reg path | Audit `report_exceptions`; never false-path between synchronous registers |
| WHS suddenly negative after CTS | Buffer insertion increased clock latency, no hold buffers added | Let CTS engine add hold buffers; verify `report_clock_skew` ≤ uncertainty |
| Slack changes by ~10% between PT and tool-native STA | Different derate / CRPR settings | Align `set_timing_derate` and CRPR enable across tools; see `references/ocv-aocv-pocv.md` |
| Worst path is on a "static config" register | Missing `set_false_path -from cfg_*` or `set_case_analysis` | Apply in `timing-constraints` skill, not here |
| Latch-based path reports zero slack but design fails | Time borrow not modeled — STA assumed flop semantics | Enable transparent-latch timing; see `references/latch-timing.md` |
| Setup OK at typical, fails at slow-slow | MMMC views not exercised | Add slow-slow setup view to signoff script; see `references/mmmc-corners.md` |
| Hold OK at slow-slow, fails at fast-fast | Hold-corner missing from signoff | Add fast-fast hold view |
| SI on → +30 ps delta on clock net | Aggressor on clock spine | Re-route clock with shielding, or add `set_si_noise_*` exceptions and rerun |
| CRPR credit looks suspiciously large | CRPR computed on a path with non-common reconvergence | Verify `report_crpr`; some tools over-credit on muxed clocks |
| OCV derate applied but slack barely moved | Flat OCV under-models depth — use AOCV/POCV | Switch to AOCV/POCV per foundry deck |

## Decision: which derating model

| Node | Model | Why |
|---|---|---|
| 90nm+ | Flat OCV (`set_timing_derate`) | Variation small; pessimism acceptable |
| 28–65nm | AOCV (depth + distance tables) | Flat OCV too pessimistic; AOCV credits depth |
| ≤16nm | POCV/SOCV (per-cell σ) | Statistical variation; AOCV under-models random Vth |

See `references/ocv-aocv-pocv.md` for the math and tool invocations.

## Master-level pitfalls

- **CRPR is not free margin.** It removes pessimism the tool added; turning
  it on doesn't make the design faster, it just stops it from being slower
  than reality. If a path needs CRPR to meet, it has zero real margin.
- **Useful skew is a loan, not income.** Borrowing from the next stage to
  pay for this one only works if the next stage has slack. Audit the
  cone before enabling.
- **Multicycle setup ⇒ multicycle hold.** Forgetting the `-hold` companion
  is the #1 STA bug — the design appears closed but silicon fails on hold.
- **MMMC ≠ pick-the-worst.** Setup and hold close at *different* corners.
  A single "worst case" corner is wrong on at least one of them.
- **Derate doesn't replace OCV models.** `set_timing_derate 1.05` does not
  give you AOCV — it gives you flat OCV with a custom factor.

## Citations

- **SDC 1.9** — `set_timing_derate`, `set_clock_uncertainty`, `set_propagated_clock`:
  command semantics normative across PrimeTime / Tempus / Vivado.
- **IEEE Std 1801 (UPF)** — when power-domain crossings affect timing,
  level-shifter delays must be in the timing arc.

## See also

- `references/timing-paths.md` — startpoints, endpoints, four path groups,
  launch/capture model.
- `references/setup-hold-equations.md` — full slack derivation with worked
  numerical example and sanity checklist.
- `references/clock-uncertainty.md` — skew (global/local), jitter (period,
  cycle-to-cycle, long-term), `set_clock_uncertainty` budget breakdown.
- `references/ocv-aocv-pocv.md` — flat OCV → AOCV → POCV/SOCV derating
  models; when each is sign-off-mandated.
- `references/crpr.md` — Clock Reconvergence Pessimism Removal; what it
  credits and what it doesn't.
- `references/latch-timing.md` — level-sensitive timing, time borrowing,
  `set_max_time_borrow`.
- `references/mmmc-corners.md` — PVT corners, RC corners, modes; setup vs
  hold corner picking.
- `references/si-crosstalk.md` — aggressor/victim, delta-delay, noise on
  clock; SI-aware STA invocation.
- `references/report-timing-deepdive.md` — reading every field of
  `report_timing -path_type full_clock_expanded`.
- `references/useful-skew.md` — intentional skew for closure; opportunistic
  vs constrained; CTS hint commands.
- `examples/pipelined_alu/` — small datapath with a setup violation,
  pipelined to fix, with self-checking TB and a synthetic timing report.
- `timing-constraints` skill — SDC/XDC authoring (writes the file this
  skill reads).
- `clock-domain-crossing` skill — structural CDC checks before STA.
