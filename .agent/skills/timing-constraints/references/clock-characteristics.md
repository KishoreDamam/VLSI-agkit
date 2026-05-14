# Clock Characteristics — Latency, Uncertainty, Transition, Sense

> Beyond `create_clock`: the SDC commands that model real-world clock behaviour
> (propagation delay, jitter, slew, unateness, ideal networks). Pre-CTS vs
> post-CTS values are *different* — this document spells out which apply when.

## The clock-model layer cake

A `create_clock` declares an *ideal* clock — perfect edges, zero latency,
infinite drive. Real clocks are not ideal. SDC layers additional commands
on top of `create_clock` to model:

| Layer | SDC commands | Models |
|---|---|---|
| Latency | `set_clock_latency`, `set_propagated_clock` | Propagation delay through clock tree |
| Uncertainty | `set_clock_uncertainty` | Jitter, skew, margin (what STA can't compute) |
| Transition | `set_clock_transition`, `set_input_transition` | Slew on the clock net |
| Sense | `set_clock_sense` | Polarity through XOR-like non-unate cells |
| Ideal | `set_ideal_network` | Carve out a region that shouldn't be analyzed |

You'll typically set most of these; missing any one can mean either
over-margining or under-margining.

## Clock latency — source vs network

Clock arrival at a flop's CK pin has two delay components:

```
   Off-chip clock source
         │
         │     ── source latency (off-chip cable, board, package)
         │
   ── port where create_clock is declared
         │
         │     ── network latency (on-chip clock tree)
         │
   ── flop's CK pin
```

| Component | When you set it | When the tool computes it |
|---|---|---|
| **Source latency** | Off-chip flight time, package delay | Never auto-computed |
| **Network latency** | Pre-CTS estimate | Post-CTS via `set_propagated_clock` |

```tcl
# Source latency — off-chip path from oscillator to chip port
set_clock_latency -source 0.5 [get_clocks clk_in]

# Source latency with early/late asymmetry
set_clock_latency -source -early 0.5 [get_clocks clk_in]
set_clock_latency -source -late  1.0 [get_clocks clk_in]

# Network latency — pre-CTS estimate of on-chip clock tree
set_clock_latency 0.3 [get_clocks clk_core]

# Network latency on a sub-tree (everything in fanout of pin X)
set_clock_latency 0.1 [get_pins clk_div/CK]
```

**Critical rule for the flow**:

1. **Pre-CTS**: use `set_clock_latency` (network) as an estimate, because
   no real clock tree exists yet.
2. **Post-CTS**: switch to `set_propagated_clock` — the tool computes
   network latency from the actual tree.
3. Source latency stays declared in both phases (the off-chip path
   doesn't change during CTS).

```tcl
# Post-CTS: replace estimate with real
set_propagated_clock [get_clocks clk_core]
# No more `set_clock_latency 0.3 ...` for this clock's network portion
```

Forgetting step 2 is a classic over-pessimism source — STA adds the
estimated network latency on top of the real tree delay.

## Clock uncertainty — jitter, skew, margin

`set_clock_uncertainty` is the catch-all for everything STA cannot
compute precisely. See `sta` skill `references/clock-uncertainty.md` for
the full budget breakdown.

```tcl
# Pre-CTS budget — generous (covers est. skew + jitter + margin)
set_clock_uncertainty -setup 0.250 [get_clocks clk_core]
set_clock_uncertainty -hold  0.080 [get_clocks clk_core]

# Post-CTS — only jitter + margin remain (real skew now computed)
set_clock_uncertainty -setup 0.100 [get_clocks clk_core]
set_clock_uncertainty -hold  0.050 [get_clocks clk_core]

# Per-clock-pair (refines inter-clock budget independently)
set_clock_uncertainty -setup -from [get_clocks clk_a] \
                              -to   [get_clocks clk_b] 0.150
```

| When | Setup uncertainty | Hold uncertainty |
|---|---|---|
| Pre-CTS | 200–400 ps | 50–150 ps |
| Post-CTS | 50–150 ps | 30–80 ps |

## Clock transition (slew)

`set_clock_transition` forces a fixed slew at every point on the clock
network — used pre-CTS to prevent the tool from computing a ridiculous
slew on a multi-thousand-fanout net.

```tcl
# Pre-CTS: assume CTS will hold clock slew at this value
set_clock_transition 0.100 [get_clocks clk_core]
```

`set_input_transition` (covered separately in
`port-electrical-constraints.md`) sets transition at one specified
point; the rest is computed. Don't use `set_input_transition` on a
clock pre-CTS — the huge fanout will give an unrealistic computed
slew at downstream points.

| Phase | Use | Don't use |
|---|---|---|
| Pre-CTS | `set_clock_transition` (forced everywhere) | `set_input_transition` on clock |
| Post-CTS | `set_input_transition` on clock port (tool computes the rest) | `set_clock_transition` (overrides real values) |

## Clock sense and unateness

A clock buffer is *positive unate*: rising in → rising out. An inverter
is *negative unate*: rising in → falling out. STA can follow either —
it just tracks the polarity along the path.

```
   clk ──[BUF]──[INV]──[BUF]──→ flop CK    (negative unate overall)
```

Some structures are **non-unate** — an XOR with a non-constant other
input, for example. STA cannot determine the polarity at the output
because it depends on both inputs.

```tcl
# Force STA to consider only the positive sense at this pin
set_clock_sense -positive [get_pins XOR1/Z]

# Force only the negative sense
set_clock_sense -negative -clock [get_clocks clk_b] [get_pins XOR2/Z]

# Stop the clock from propagating beyond this point in this mode
set_clock_sense -stop_propagation -clock [get_clocks clk_test] [get_pins MUX/Y]
```

**When you need `set_clock_sense`:**

- Clock-mux outputs where one input is "the clock" and the other is
  combinational logic — XOR-style behaviour, non-unate.
- Pulse-generator outputs (AND of clk and delayed-clk) — non-unate.
- Mode-specific propagation: in scan mode, stop the functional clock
  from reaching scan-only flops.

The `-pulse` form generates a pulse waveform without a separate
`create_generated_clock`:

```tcl
set_clock_sense -pulse rise_triggered_high_pulse [get_pins AND1/Z]
set_clock_latency -rise 0.2 [get_pins AND1/Z]
set_clock_latency -fall 0.9 [get_pins AND1/Z]
# Pulse width = |rise_latency − fall_latency| = 0.7
```

## Ideal networks

`set_ideal_network` declares a region of the design that should not be
analyzed for design rules (max cap, max fanout, max transition) — the
tool propagates "ideal" forward.

Common targets:

- **Scan-enable** — huge fanout, but only active during test. Mark as
  ideal so synth doesn't waste effort buffering it.
- **Reset trees** before CTS — reset CTS happens separately; ideal
  prevents premature buffering.
- **Test-mode pins** — same reasoning.

```tcl
set_ideal_network [get_pins scan_enable_reg/Q]

# Stop ideal propagation at this point
set_ideal_network -no_propagate [get_pins clk_gate/EN]

# Set explicit ideal transition / latency
set_ideal_transition 0.150 [get_pins scan_enable_reg/Q]
set_ideal_latency    0.000 [get_pins scan_enable_reg/Q]
```

**Trap**: ideal propagates through combinational logic by default. If
the propagation crosses into a region that *should* be timed, you'll
silently lose timing analysis there. Always audit with
`report_design -idle` or equivalent after declaring ideal networks.

## Putting it together — typical SDC by phase

### Pre-CTS

```tcl
# Primary clocks
create_clock -name clk_core -period 1.000 [get_ports clk_in]

# Source latency (off-chip, doesn't change)
set_clock_latency -source -early 0.4 [get_clocks clk_core]
set_clock_latency -source -late  0.6 [get_clocks clk_core]

# Network latency — pre-CTS estimate
set_clock_latency 0.300 [get_clocks clk_core]

# Forced clock slew pre-CTS
set_clock_transition 0.080 [get_clocks clk_core]

# Generous uncertainty
set_clock_uncertainty -setup 0.250 [get_clocks clk_core]
set_clock_uncertainty -hold  0.080 [get_clocks clk_core]

# Scan-enable ideal
set_ideal_network [get_pins scan_en_reg/Q]
```

### Post-CTS

```tcl
# Primary clocks — same as pre-CTS
create_clock -name clk_core -period 1.000 [get_ports clk_in]

# Source latency — still declared
set_clock_latency -source -early 0.4 [get_clocks clk_core]
set_clock_latency -source -late  0.6 [get_clocks clk_core]

# Network latency now COMPUTED from real tree
set_propagated_clock [get_clocks clk_core]

# Drop set_clock_transition; let tool compute from real tree
# (or use set_input_transition on the clock port)
set_input_transition 0.050 [get_ports clk_in]

# Tighter uncertainty — only jitter + margin remain
set_clock_uncertainty -setup 0.100 [get_clocks clk_core]
set_clock_uncertainty -hold  0.050 [get_clocks clk_core]

# Reset/scan ideal networks usually removed at this phase too,
# replaced by real buffering
```

## Common pitfalls

- **`set_clock_latency` and `set_propagated_clock` both active**. The
  tool adds them. Always remove the pre-CTS network estimate when you
  switch to propagated clocks.
- **Source latency dropped post-CTS**. CTS doesn't touch off-chip paths,
  but engineers sometimes wipe the whole `set_clock_latency` block.
  Source latency must stay.
- **`set_clock_transition` left in post-CTS scripts.** It overrides the
  real (now-propagated) transition values — over-margin or
  under-margin depending on direction.
- **Uncertainty not reduced post-CTS.** The pre-CTS budget covered
  estimated-skew + jitter + margin; with real skew now in latency,
  uncertainty should drop or you stack pessimism.
- **`set_ideal_network` propagation runs further than expected.**
  Audit; use `-no_propagate` to bound the region.
- **Non-unate clock without `set_clock_sense`.** STA emits a warning and
  guesses; the wrong polarity silently throws timing off.
- **Pulse via `set_clock_sense -pulse` without latency.** Without
  rise/fall latency the pulse width is zero — the analysis behaves
  like no pulse at all.

## Citations

- **SDC 1.9** — `set_clock_latency`, `set_propagated_clock`,
  `set_clock_uncertainty`, `set_clock_transition`, `set_clock_sense`,
  `set_ideal_network`, `set_ideal_transition`, `set_ideal_latency`.
- **Gangadharan & Churiwala**, *Constraining Designs for Synthesis and
  Timing Analysis* (Springer 2013), Chapter 8.

## See also

- `clock-declarations.md` — `create_clock`, `create_generated_clock`,
  virtual clocks.
- `io-delays.md` — `set_input_delay` / `set_output_delay` with clock
  associations.
- `port-electrical-constraints.md` — `set_input_transition`,
  `set_load`, etc.
- `sta` skill `references/clock-uncertainty.md` — how uncertainty
  budget is built from PLL jitter + CTS skew + margin.
- `sta` skill `references/ocv-aocv-pocv.md` — derating; don't
  double-count with uncertainty.
