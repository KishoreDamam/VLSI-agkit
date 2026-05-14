# Setup/Hold Equations

> Full derivation of slack with a worked numerical example. Memorize the form
> and you can reconstruct any `report_timing` row from first principles.

## Setup check

For a register-to-register path, the capture register must see stable data
at its D pin **at least `T_setup` before** the capture clock edge:

```
T_launch_clk_arrival + T_cq + T_logic + T_setup
  ≤ T_capture_clk_arrival + T_period
```

Rearranging for slack:

```
Setup slack = (T_capture_clk_arrival + T_period - T_uncertainty)
            - (T_launch_clk_arrival + T_cq + T_logic + T_setup)
            + T_CRPR_credit
```

Decomposition:

| Term | Meaning |
|---|---|
| `T_period` | Clock period (or capture edge time minus launch edge time for unbalanced clocks) |
| `T_skew = T_capture_clk - T_launch_clk` | Clock-network arrival difference (positive helps setup) |
| `T_uncertainty` | `set_clock_uncertainty` value (jitter + margin) |
| `T_cq` | Clock-to-Q of the launch register (from `.lib`) |
| `T_logic` | Combinational delay through the data path |
| `T_setup` | Setup time of the capture register (from `.lib`) |
| `T_CRPR_credit` | Pessimism removed for common clock-path portion |

## Hold check

The capture register must see stable data **at least `T_hold` after** the
*same* clock edge that fired the launch:

```
T_launch_clk_arrival + T_cq + T_logic
  ≥ T_capture_clk_arrival + T_hold
```

Slack:

```
Hold slack  = (T_launch_clk_arrival + T_cq + T_logic)
            - (T_capture_clk_arrival + T_hold + T_uncertainty)
            + T_CRPR_credit
```

Key contrast vs setup:

- Hold is the **same edge** at launch and capture — `T_period` does not
  appear. Hold cares about how *fast* data races through, not how slow.
- Positive skew (capture later than launch) **hurts** hold. Common cause
  of hold violations after CTS: leaf-cell skew widens.
- Hold uses **min delays** (best-case cell delay). Setup uses **max**.

## Worked example — reg-to-reg, 1 GHz clock

Setup. Process: 28nm. Library: typical-typical, 0.9 V, 25 °C.

```
T_period                    = 1000 ps
T_launch_clk_arrival         =  120 ps   (clock tree latency to launch)
T_capture_clk_arrival        =  130 ps   (clock tree latency to capture)
T_skew                       =   10 ps   (capture later, helps setup)
T_uncertainty                =   80 ps   (jitter + margin, see clock-uncertainty.md)
T_cq                         =  100 ps   (DFF Q→D launch flop)
T_logic                      =  650 ps   (5 LUT4 + routing)
T_setup                      =   50 ps   (DFF setup)
T_CRPR_credit                =   15 ps   (common clock path of 100 ps × 15% derate)
```

Substitute into the setup equation:

```
Required = T_capture_clk_arrival + T_period - T_uncertainty
         = 130 + 1000 - 80
         = 1050 ps

Arrival  = T_launch_clk_arrival + T_cq + T_logic + T_setup - T_CRPR_credit
         = 120 + 100 + 650 + 50 - 15
         = 905 ps

Setup slack = Required - Arrival
            = 1050 - 905
            = +145 ps   ← PASS
```

Now hold on the same path. Use *min* delays:

```
T_cq_min      =  70 ps
T_logic_min   = 480 ps
T_hold        =  20 ps
T_uncertainty =  30 ps   (hold uncertainty is usually smaller)
```

```
Launch  = T_launch_clk_arrival + T_cq_min + T_logic_min - T_CRPR_credit
        = 120 + 70 + 480 - 15
        = 655 ps

Required = T_capture_clk_arrival + T_hold + T_uncertainty
         = 130 + 20 + 30
         = 180 ps

Hold slack = Launch - Required
           = 655 - 180
           = +475 ps   ← PASS (huge margin, typical for reg2reg)
```

## Multicycle setup

If you declared `set_multicycle_path 3 -setup`, the capture edge moves
**two** periods later (N−1 cycles, since by default the capture is
already at +1 period):

```
T_period_effective_setup = N * T_period = 3 * 1000 = 3000 ps
```

But you **must** also declare `set_multicycle_path 2 -hold` so hold check
is not also shifted — otherwise the hold edge moves to T = 2 × period and
the design will fail hold on silicon. See `timing-constraints` skill.

## Hold formula sanity check

A common confusion: "why does skew hurt hold?" Look at the inequality:

```
T_launch_clk + T_cq_min + T_logic_min ≥ T_capture_clk + T_hold
```

If capture clock arrives later (`T_capture_clk > T_launch_clk`), the
right-hand side grows — data must take *longer* to be safe. Fast logic
+ late capture clock = hold race.

## Sanity checklist before fixing a violation

Before rewriting RTL or adding a multicycle, sanity-check the equation:

1. **Is the period in the report what you expect?** A wrong `create_clock`
   period dominates everything else.
2. **Is `T_uncertainty` realistic?** A 5 ps value at 28 nm is fantasy; an
   800 ps value at 100 MHz is paranoid. See `clock-uncertainty.md`.
3. **Is `T_cq + T_setup` close to the library number?** If much larger,
   the wrong corner is loaded.
4. **Is `T_logic` plausible for the gate count?** A 50-LUT path with
   T_logic=200 ps means the report is wrong or the library is mis-scaled.
5. **Is CRPR credit shown?** If absent on a multi-buffered clock tree,
   CRPR is disabled — slack is over-pessimistic.
6. **Is derate applied?** `report_timing -derate` field should show the
   numbers; missing derate at 28nm+ means signoff is unsafe.

If all six pass, then the violation is real and you need a physical or RTL
fix. If any fails, fix the constraint or settings first — most
"violations" disappear here.

## See also

- `timing-paths.md` — what launch/capture edges mean.
- `clock-uncertainty.md` — what goes into `T_uncertainty`.
- `crpr.md` — when CRPR credit applies.
- `report-timing-deepdive.md` — mapping equation terms to report fields.
