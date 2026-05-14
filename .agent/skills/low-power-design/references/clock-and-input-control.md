# Clock & Input Control for Dynamic Power

> Dynamic power = α·C·V²·f. On an FPGA, the system clock is the highest
> fanout net in the design — every cycle it doesn't toggle saves the most
> power. This reference is about *how* to stop it toggling cleanly, and
> the related input-buffer power leak.

## Why dynamic power on FPGAs concentrates in the clock

A typical FPGA design has thousands of flops on one clock. Every clock
edge charges/discharges every flop's clock-input capacitance plus all
downstream node capacitance that toggles. Empirically:

| Source | Share of dynamic power |
|---|---|
| Clock tree + flop clock inputs | 30–60 % |
| Combinational logic switching | 20–40 % |
| I/O buffers | 5–25 % |
| Block-RAM and DSP toggling | 5–15 % |

Stopping the clock in idle regions is therefore the single biggest
power lever. There are three good ways and one bad way to do it.

## Three good ways

### 1. Clock-enable on the flop (best)

Most flops in the FPGA fabric have a CE pin. When `CE = 0`, the flop
holds its value; the clock keeps toggling but the flop's *output*
doesn't move. Downstream combinational logic doesn't switch either
(because its inputs are stable). Power saving comes from quiescent
fanout cone, not from quieting the clock.

```systemverilog
always_ff @(posedge clk)
    if (enable)
        data_q <= next_data;
```

Synthesis maps this directly to the flop's CE pin. No new clock domain,
no skew issue, STA fully analyzes the path.

**Caveat**: doesn't reduce clock-tree power itself. The clock tree
still toggles. If clock-tree power dominates, you need approach 2 or 3.

### 2. Global clock mux (BUFGMUX / GBUFCE)

A dedicated mux primitive selects between two clocks (or a clock and
ground). On Xilinx: `BUFGCTRL` / `BUFGMUX`. On Intel/Altera:
`ALTCLKCTRL` with enable input. Output drives a low-skew global net.

```systemverilog
// Xilinx primitive
BUFGMUX BUFGMUX_inst (
    .O  (clk_gated),
    .I0 (clk_main),
    .I1 (1'b0),          // off state
    .S  (clk_enable)
);
```

When `S = 0`, the gated clock is held at constant; downstream fanout
sees no edges. Real dynamic power saving on the clock tree itself.

**Why this works where logic gating doesn't**: BUFGMUX is engineered to
switch its select line cleanly (glitch-free). The output goes to a
*dedicated* low-skew clock spine — same skew budget as the main clock.

### 3. Clock-enable in BUFGCE / global clock buffers

A simpler primitive: a global clock buffer with an enable input. Output
follows input only when enabled; gated cleanly. No mux semantics, just
on/off.

```systemverilog
BUFGCE BUFGCE_inst (
    .O  (clk_gated),
    .I  (clk_main),
    .CE (active_mode)
);
```

Same low-skew clock spine, same glitch-free guarantee. Use BUFGCE when
you don't need a second clock source.

## The bad way — direct clock gating with logic

```systemverilog
// ❌ ANTI-PATTERN
assign clk_gated = clk & enable;

always_ff @(posedge clk_gated)
    data_q <= next_data;
```

This compiles. The problem is *physical*:

- **`clk_gated` is not on a global clock route.** Synth maps it through
  general routing — much higher skew. Skew between flops driven by
  `clk_gated` can exceed any combinational delay → hold violations.
- **Enable signal glitches propagate as clock edges.** Any momentary
  glitch on `enable` while `clk = 1` produces a spurious clock edge on
  `clk_gated`. Synchronous design assumption violated.
- **Synthesis tool may "fix" it for you** by removing the gate (Synplify
  default) — silently, so your power-saving intent disappears.
- **STA tools struggle.** The new "clock" needs to be declared as a
  generated clock; uncertainty budgets become guesswork; SI analysis
  loses correlation.

The book's Figure 3.4 example shows the catastrophic case: 1 ns data
path, 2 ns clock-gated routing path. Data races through two stages on
one edge → silicon-level functional failure.

**Rule:** if your library / FPGA has a clock-control primitive, use it.
Don't gate clocks with logic.

## Hold violations on FPGAs (rare but real)

FPGAs usually have built-in delays on the routing fabric that make hold
violations rare in normal use. The exception is clock-tree delay — when
the clock takes longer to arrive than the data does. Direct clock
gating with logic creates exactly this scenario.

If you must use a logic-gated clock for legacy reasons:

1. Constrain it as a generated clock (`create_generated_clock`).
2. Run STA explicitly for hold; expect the tool to insert delay buffers
   on the data path to align timing.
3. Verify that the tool's "fixes" don't get optimized away in a
   subsequent compile pass.

This is a lot of fragility for a power saving you can get for free with
a primitive. Don't do it unless the toolchain forces you.

## Input control — minimize transition time

CMOS input buffers leak current during transition: both the NMOS and
PMOS conduct simultaneously when the input is between Vth and (Vdd −
Vth). Slow-transitioning inputs spend more time in this conducting
state → more power lost.

```
        Vdd
         │
         ├─── PMOS  ─── conducts when input is low
   IN ───┤
         ├─── NMOS  ─── conducts when input is high
         │
        GND

  During slow input transition, BOTH conduct for some time → shoot-through current.
```

Steady-state CMOS inputs leak only sub-threshold current. Transition
power scales with **transition time**: faster slew → less time in the
conducting overlap region → less power per transition.

### Practical rules

- **Don't underdrive an input.** A 1.8 V signal driving a 2.5 V input
  may sit between Vth and (Vdd − Vth) — both transistors saturate
  partially → continuous current draw. Match voltage standards.
- **Don't leave inputs floating.** Floating inputs may settle at a
  metastable voltage with both transistors conducting. Use FPGA-internal
  pull-up / pull-down resistors via the IOSTANDARD attribute.

```tcl
# Xilinx XDC — terminate unused inputs
set_property IOSTANDARD LVCMOS18 [get_ports unused_in]
set_property PULLUP    TRUE     [get_ports unused_in]
```

- **Drive inputs with matched voltage levels.** If level-shifters are
  needed, use FPGA-specific level-shifter primitives, not RC dividers.
- **Minimize input slew via series termination** on noisy traces (see
  `voltage-dual-edge-termination.md`).

### When this matters most

Input-buffer transition power dominates when:

- The FPGA has many high-toggle-rate inputs (LVDS RX, fast SerDes data
  pins) — sum of all input dynamic power ≈ clock tree.
- Inputs are underdriven (analog signal, level mismatch).
- Inputs are floating (always — power-on default state).

For a typical FPGA design with mostly low-toggle inputs, this is a 5–15
% saving — significant but secondary to clock control.

## Clock-enable architecture patterns

When you have many modules and want to power-gate them dynamically:

### Hierarchical CE

```systemverilog
// Top-level — coarse enable
wire blk_a_active = mode_select == MODE_A;
wire blk_b_active = mode_select == MODE_B;

block_a u_blk_a (.ce(blk_a_active), .clk(clk), ...);
block_b u_blk_b (.ce(blk_b_active), .clk(clk), ...);
```

```systemverilog
// Inside block_a — fine-grained CE
always_ff @(posedge clk)
    if (ce & inner_enable)
        ...
```

Fewer global clock buffers consumed than the BUFGCE approach; reaches
finer granularity at no extra primitive cost.

### When BUFGCE wins over CE

BUFGCE actually quiets the clock tree itself. If your power analysis
shows clock-tree power dominates (typical at ≥ 60 % utilization), even
fully CE-gating the design doesn't reduce the clock-spine consumption.
A BUFGCE shuts off the spine. Use it for whole-block power down where
the block is *off* for milliseconds, not just inactive for cycles.

## Citations

- **Kilts**, *Advanced FPGA Design: Architecture, Implementation, and
  Optimization*, Wiley 2007, Chapter 3 — clock gating, input control,
  CMOS transition power.
- **Xilinx UG472** — 7 Series Clocking Resources: `BUFGCTRL`,
  `BUFGMUX`, `BUFGCE`.
- **Intel/Altera Cyclone V Handbook** — `ALTCLKCTRL` clock control
  block.

## See also

- `voltage-dual-edge-termination.md` — voltage scaling, DDR registers,
  series termination, decoupling.
- `clock-domain-crossing` skill — clock-mux selection and metastability.
- `dft-patterns/references/scan-chains.md` — gated clocks need
  `TE`-aware ICG for scan.
- `clean-rtl/references/synchronous-reset.md` — reset coding with
  clock-enable interaction.
