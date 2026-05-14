# Port Electrical Constraints

> `set_input_delay` / `set_output_delay` tell STA *when* a signal arrives.
> The commands here tell STA *how* it arrives (drive strength, transition)
> and *what it sees* (load, fanout). Without them, the tool assumes
> idealized drivers and loads, and over-optimizes.

## What these constraints are for

STA computes transition (slew) times across the design from driver
strength and load capacitance. At an input port the driver lives
*outside* the block — STA doesn't know its electrical characteristics
unless you tell it. Same for output ports: the load lives outside.

If you don't tell STA:

- It assumes infinite drive and zero external load (overly optimistic).
- Slew at the input port is artificially fast — interior paths look
  faster than they will be in silicon.
- Output ports drive into a zero-cap load — looks faster than real.

The result: synthesis under-sizes drivers at boundaries, hold-time
buffers go missing, silicon fails.

## Five commands, three jobs

| Job | Commands | What it sets |
|---|---|---|
| **Driver model** at input port | `set_drive`, `set_driving_cell` | Drive resistance / cell that drives this input |
| **Slew** directly | `set_input_transition` | Skip the driver model, give the slew directly |
| **External load** at output port | `set_load`, `set_fanout_load`, `set_port_fanout_number` | Capacitive load the output drives |

You pick one per port for the driver job (drive vs driving_cell vs
input_transition) and one for the load job (load vs fanout_load vs
fanout_number).

## `set_drive` — driver as a resistor

The simplest driver model: a Thevenin resistance.

```tcl
set_drive  [-rise] [-fall]
           [-min] [-max]
           resistance_value port_list
```

```tcl
# Driver presents 100 Ω to the input port (both edges, both corners)
set_drive 100 [get_ports data_in*]

# Different resistance for rise vs fall (asymmetric NMOS/PMOS)
set_drive 80  -rise [get_ports req]
set_drive 120 -fall [get_ports req]
```

Higher resistance = weaker driver = slower transition. The value is
inverse drive strength — the name `set_drive` is misleading.

**When used:** rarely in modern flow. Useful for quick, library-free
estimates and for analog/mixed-signal inputs with known Thevenin
drivers. Most teams use `set_driving_cell` instead.

## `set_driving_cell` — driver as a library cell

You name the cell that drives the input. STA looks up its electrical
characteristics from the library:

```tcl
set_driving_cell       [-lib_cell lib_cell_name]
                       [-rise] [-fall]
                       [-min] [-max]
                       [-library lib_name]
                       [-pin pin_name]
                       [-from_pin from_pin_name]
                       [-multiply_by factor]
                       [-dont_scale]
                       [-no_design_rule]
                       [-clock clock_name]
                       [-clock_fall]
                       [-input_transition_rise rise_time]
                       [-input_transition_fall fall_time]
                       port_list
```

Most-used form:

```tcl
set_driving_cell -lib_cell BUFX2 [get_ports data_in*]
```

Common option combinations:

| Option | Use case |
|---|---|
| `-lib_cell` | (always) name of the cell |
| `-pin` | Cell has multiple outputs; pick which one drives |
| `-from_pin` | Cell has multiple input arcs; pick the relevant arc |
| `-library` | Disambiguate when multiple libraries loaded |
| `-multiply_by` | Driver fanout is split across multiple loads — derates strength |
| `-clock`, `-clock_fall` | Driving-cell only applies for `set_input_delay` w/ matching clock |
| `-input_transition_rise/fall` | Drive arc characterized at this input slew |
| `-no_design_rule` | Don't propagate driver's max-cap / max-fanout rules to the port |

### Per-clock driving cells

When an input has `set_input_delay` against multiple clocks, you can
specify a different driving cell per clock:

```tcl
set_input_delay -clock clk_a 2.0 [get_ports data_in]
set_input_delay -clock clk_b 3.0 [get_ports data_in] -add_delay

set_driving_cell -lib_cell MUX21 -from_pin A -clock clk_a [get_ports data_in]
set_driving_cell -lib_cell MUX21 -from_pin B -clock clk_b [get_ports data_in]
```

For paths from `clk_a`, the A→Z arc characterizes the slew; for paths
from `clk_b`, the B→Z arc. Useful for mux'd input scenarios.

### Multi-load attenuation

If the driver's full strength serves multiple sinks, the strength
*available* for your input is reduced. Use `-multiply_by`:

```tcl
# Driver drives 4 loads, only one is our port
set_driving_cell -lib_cell BUFX4 -multiply_by 4 [get_ports my_input]
```

Better: model with `set_load` on the original net to capture the actual
loading, rather than scaling the driver.

## `set_input_transition` — slew directly

Skip the driver model and just declare the slew:

```tcl
set_input_transition   [-rise] [-fall]
                       [-min] [-max]
                       [-clock clock_name]
                       [-clock_fall]
                       transition port_list
```

```tcl
# Quick: all inputs see 200 ps transition
set_input_transition 0.200 [all_inputs]

# Asymmetric rise / fall
set_input_transition -rise 0.100 [get_ports data_in*]
set_input_transition -fall 0.150 [get_ports data_in*]
```

**`set_input_transition` vs `set_clock_transition`** (a frequent
confusion):

| | `set_input_transition` | `set_clock_transition` |
|---|---|---|
| Where applied | One specific port/pin | An entire clock network |
| Propagation | Tool computes slew at downstream points | Slew is *forced* identical at every point |
| Use | Post-CTS, data ports, single-fanout clocks | Pre-CTS, high-fanout clocks |

For data ports, always `set_input_transition` (or a driving-cell model).
For clocks, use `set_clock_transition` pre-CTS to avoid computing a
catastrophic slew on the unrooted clock fanout; switch to
`set_input_transition` (on the clock port) after CTS so the propagated
tree's real slew flows through STA.

## `set_load` — output capacitive load

```tcl
set_load  [-min] [-max]
          [-subtract_pin_load]
          [-pin_load]
          [-wire_load]
          value objects
```

```tcl
# Output port drives an external 2 pF load
set_load 2.0 [get_ports data_out*]

# Asymmetric setup vs hold
set_load -min 0.5 -max 2.0 [get_ports addr*]

# Annotate post-layout net capacitance on internal net
set_load 0.15 [get_nets long_routed_net]
```

`-pin_load` and `-wire_load` separate the load into the destination
pin's input cap and the wire cap. `-subtract_pin_load` is for
back-annotation where you have total net cap and want to subtract the
already-known pin caps.

For internal nets, `set_load` is how you back-annotate extracted post-
layout parasitics into a pre-layout SDC.

## `set_fanout_load` and `set_port_fanout_number`

Two related but distinct metrics:

```tcl
# Number of pins driven (integer count)
set_port_fanout_number 8 [get_ports clk_div]

# Total external load expressed in units of standard-load
set_fanout_load 2.5 [get_ports data_out]
```

**`set_port_fanout_number`** — count of pins. Affects wire-load model
estimates that depend on fanout count.

**`set_fanout_load`** — total external load in multiples of the
library's standard load. Different pins have different input cap; a
buffer's input might be 1 standard load, an AND gate's input 1.5.
Drives the same calculation as `set_load`, just in different units.

Use `set_load` when you know the actual capacitance. Use
`set_fanout_load` when you only know how many fanout pins (and roughly
their types) but not their absolute cap. Use `set_port_fanout_number`
for wire-load-model-based flows that need a pin count.

## When to set what — quick guide

| Phase / situation | Inputs | Outputs |
|---|---|---|
| Front-end synthesis estimate | `set_driving_cell` of a typical buffer | `set_load` of typical fanout cap |
| Detailed sign-off | `set_driving_cell` matching the actual upstream block's driver | `set_load` from real extraction |
| Quick prototyping | `set_input_transition 0.1` (all_inputs) | `set_load 0.05` (all_outputs) |
| Mixed-signal / analog input | `set_drive` with measured Thevenin R | `set_load` with measured cap |

## Common pitfalls

- **No port constraints at all.** Tool assumes ideal drivers / zero
  loads → boundary paths look way too fast. After tape-out, silicon
  hold-violates everywhere.
- **`set_driving_cell` without `-pin`** on a multi-output cell. Tool
  picks an arbitrary output arc — results vary tool to tool.
- **`set_input_transition` on a clock port pre-CTS.** Unbounded fanout
  makes the computed downstream slew enormous; use
  `set_clock_transition` instead until CTS is done.
- **`set_load` ignored due to `set_fanout_load` on the same port.** The
  tool resolves ambiguity arbitrarily. Pick one method per port and
  stick to it.
- **Driver-cell library not loaded.** `-lib_cell` reference dangles;
  some tools error, others silently fall back to a default. Audit
  `report_input_delay` for missing models.
- **Forgetting `-rise`/`-fall` asymmetry on outputs that drive a
  pull-up resistor.** Pull-ups have asymmetric drive strength; one
  transition is much slower than the other.
- **`set_drive 0`**. Means *infinite* drive (zero resistance). Drops
  any meaningful timing on the input.

## Validation

```tcl
report_port -driver_load        ;# shows what driver / load is in effect
check_timing -include {no_driving_cell no_input_delay no_output_delay}
```

After applying constraints, every port should show:

- A driver model (cell, transition, or drive resistance).
- An input or output delay.
- A load (for outputs).

`check_timing` flags any missing piece — fix all warnings before
running real STA.

## Citations

- **SDC 1.9** — `set_drive`, `set_driving_cell`, `set_input_transition`,
  `set_load`, `set_fanout_load`, `set_port_fanout_number`.
- **Gangadharan & Churiwala**, *Constraining Designs for Synthesis and
  Timing Analysis* (Springer 2013), Chapter 10.

## See also

- `clock-characteristics.md` — `set_clock_transition` (clock-net slew).
- `io-delays.md` — `set_input_delay` / `set_output_delay` for arrival
  timing.
- `sta` skill `references/report-timing-deepdive.md` — how driver /
  load show up in the timing report.
