# Clock Declarations Reference

## `create_clock` — Primary Clocks

Every independent clock source on the device boundary needs a `create_clock`.
The period is in nanoseconds; the waveform default is 50% duty cycle starting
at 0 ns.

```tcl
# 200 MHz system clock (5 ns period)
create_clock -name clk_200 -period 5.000 [get_ports clk_200_p]

# 156.25 MHz Ethernet RX clock (6.4 ns period)
create_clock -name clk_eth_rx -period 6.400 [get_ports clk_eth_rx]

# 50 MHz APB bus clock (20 ns period)
create_clock -name clk_apb -period 20.000 [get_ports clk_apb]

# Explicit 50% duty cycle (same as default, shown for clarity)
create_clock -name clk_200 -period 5.000 -waveform {0.000 2.500} \
    [get_ports clk_200_p]
```

**Vivado:** For LVDS differential inputs, specify only the P-side port. Vivado
infers the N-side from the I/O standard.

**DC / Genus:** In ASIC flows, `create_clock` points to the input pin of the
clock buffer or pad cell, not the RTL port directly.

---

## `create_generated_clock` — PLL/MMCM Outputs and Dividers

Generated clocks track their source for skew and uncertainty propagation.
Always name them explicitly so constraint references remain stable across
synthesis reruns.

```tcl
# MMCM output: 100 MHz from 200 MHz source (divide by 2)
create_generated_clock -name clk_100 \
    -source [get_pins mmcm0/CLKIN1] \
    -divide_by 2 \
    [get_pins mmcm0/CLKOUT0]

# PLL output: 400 MHz from 200 MHz source (multiply by 2)
create_generated_clock -name clk_400 \
    -source [get_pins pll0/CLKIN1] \
    -multiply_by 2 \
    [get_pins pll0/CLKOUT0]

# RTL clock divider (register toggle output)
create_generated_clock -name clk_div4 \
    -source [get_ports clk_200_p] \
    -divide_by 4 \
    [get_pins clk_div_reg/Q]
```

**Vivado:** MMCM/PLL outputs receive auto-derived generated clocks. Overriding
with an explicit `create_generated_clock` pins the name and ensures other
constraints referencing `-clock clk_100` remain valid after IP regeneration.

**Genus / Innovus:** Required when the netlist contains a custom clock divider
cell; the tool cannot infer the source relationship automatically.

---

## Virtual Clocks

A virtual clock has no physical source. Use it to constrain I/O ports whose
reference clock is not present on the device (e.g., the board drives a
DDR interface with a clock that is board-level only).

```tcl
# Virtual clock at 400 MHz for off-chip interface timing
create_clock -name vclk_ddr -period 2.500

# Then reference it in I/O delay commands
set_input_delay -clock vclk_ddr -max 0.800 [get_ports ddr_dq*]
```

Virtual clocks do not appear on real nets. `report_clocks` will show them
with "(virtual)" in the source column.

---

## `set_clock_groups` — Asynchronous and Exclusive

### Asynchronous groups

Use when clocks share no timing relationship. The tool performs no
setup/hold analysis across these groups — this is correct only when
synchronizers handle all crossings.

```tcl
# Three independent clocks — no analysis between any pair
set_clock_groups -asynchronous \
    -group [get_clocks clk_eth_rx] \
    -group [get_clocks clk_200] \
    -group [get_clocks clk_apb]
```

Each clock must appear in at most one `-group` argument. Generated clocks
derived from a source must be included in the same group as their source
if paths exist between them and unrelated domains.

### Exclusive groups (clock mux)

Use when only one clock is active at a time (e.g., a functional/test clock
mux). The tool suppresses analysis between groups but does not require
synchronizers — the assumption is the mux prevents simultaneous activity.

```tcl
set_clock_groups -exclusive \
    -group [get_clocks clk_func] \
    -group [get_clocks clk_scan]
```

### Common mistake: using `set_false_path` instead of `set_clock_groups`

`set_false_path -from clk_a -to clk_b` is directional; it must be paired
with the reverse direction to cover both setup and hold. `set_clock_groups`
is bidirectional and covers both directions in one command — prefer it for
async clock pairs.

---

## Clock Uncertainty

Explicit `set_clock_uncertainty` is rarely needed in modern flows where the
tool computes it from PLL models. Add it only when:
- Overriding a vendor model with measured jitter data.
- Adding margin for a clock source with no PLL model.

```tcl
# 100 ps additional uncertainty on clk_eth_rx (measured jitter)
set_clock_uncertainty 0.1 -setup [get_clocks clk_eth_rx]
```
