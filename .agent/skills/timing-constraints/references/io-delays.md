# I/O Delays Reference

## System-Synchronous vs Source-Synchronous

| Model | Clock relationship | Derivation |
|---|---|---|
| **System-synchronous** | Board clock drives both FPGA and external device | I/O delays come from external device spec: setup = t_co_max + t_trace; hold = t_hold_min − t_trace |
| **Source-synchronous** | FPGA or external device forwards a clock alongside data | I/O delays come from the window relative to the forwarded clock: typically ±(setup_margin + hold_margin) |

---

## `set_input_delay` — System-Synchronous

For a system clock scenario where an external device drives data to the FPGA
and both share the same board-level clock:

```
Input delay budget:
  -max (setup analysis) = t_co_max + t_trace_data − t_trace_clk_min
  -min (hold analysis)  = t_co_min + t_trace_data − t_trace_clk_max
```

```tcl
# System-synchronous input; 200 MHz board clock
# t_co_max=1.5 ns, t_trace ~0.5 ns net, no skew: -max = 2.0, -min = 0.5
set_input_delay -clock clk_200 -max 2.0 [get_ports data_in*]
set_input_delay -clock clk_200 -min 0.5 [get_ports data_in*]
```

**Negative `-min`:** A negative `-min` input delay is valid and common when
the data arrives before the clock edge at the FPGA pin. Do not be alarmed by
the sign — STA uses it correctly for hold checking.

---

## `set_output_delay` — System-Synchronous

Output delay describes how much time the receiving device needs relative to
the capturing clock edge.

```
Output delay budget:
  -max (setup analysis) = t_su_receiver + t_trace_data − t_trace_clk
  -min (hold analysis)  = t_hold_receiver − t_trace_data (may be negative)
```

```tcl
# System-synchronous output to a register outside the FPGA
set_output_delay -clock clk_200 -max 2.5 [get_ports data_out*]
set_output_delay -clock clk_200 -min -0.5 [get_ports data_out*]
```

---

## Source-Synchronous DDR Input (Double Data Rate)

In a DDR source-synchronous interface (e.g., DDR3/LPDDR4 DQ bus), the
forwarded clock (DQS strobe) samples data on both rising and falling edges.
Each edge requires its own `-max`/`-min` constraint pair using `-clock_fall`
and `-add_delay`.

### DDR3 example at 400 MHz (2.5 ns period)

Spec: setup window = 1 ns, hold window = 0.5 ns relative to DQS strobe.

```tcl
# Rising-edge capture
set_input_delay -clock clk_ddr -max 1.0 [get_ports ddr_dq*]
set_input_delay -clock clk_ddr -min 0.5 [get_ports ddr_dq*]

# Falling-edge capture (add to existing constraints, do not replace)
set_input_delay -clock clk_ddr -max 1.0 [get_ports ddr_dq*] \
    -clock_fall -add_delay
set_input_delay -clock clk_ddr -min 0.5 [get_ports ddr_dq*] \
    -clock_fall -add_delay
```

`-add_delay` is mandatory here. Without it, the falling-edge constraint
replaces the rising-edge constraint rather than adding a second analysis
window. Both edges must be covered.

### Why -max and -min matter for hold

`-max` is used for setup analysis (tightest path: data arrives latest).
`-min` is used for hold analysis (loosest path: data leaves earliest).
Omitting `-min` leaves hold unconstrained — the tool may not flag hold
violations at the I/O boundary.

---

## `set_output_delay` — Source-Synchronous DDR Output

```tcl
# Center-aligned DDR output: forwarded clock aligns to center of data eye
set_output_delay -clock clk_ddr -max 0.6 [get_ports ddr_dq*]
set_output_delay -clock clk_ddr -min -0.4 [get_ports ddr_dq*]
set_output_delay -clock clk_ddr -max 0.6 [get_ports ddr_dq*] \
    -clock_fall -add_delay
set_output_delay -clock clk_ddr -min -0.4 [get_ports ddr_dq*] \
    -clock_fall -add_delay
```

---

## Virtual Clock for Off-Chip Reference

When the I/O reference clock is not present on the device (it is consumed
by external circuitry only), use a virtual clock:

```tcl
create_clock -name vclk_ext -period 10.0
set_input_delay -clock vclk_ext -max 3.0 [get_ports ext_data*]
set_input_delay -clock vclk_ext -min 1.0 [get_ports ext_data*]
```

---

## Common Mistakes

| Mistake | Effect | Fix |
|---|---|---|
| Omitting `-add_delay` on DDR falling-edge | Replaces rising-edge constraint; one edge unconstrained | Always pair DDR falling-edge with `-add_delay` |
| Setting only `-max` input delay | Hold analysis unconstrained at I/O boundary | Always specify both `-max` and `-min` |
| Using `set_false_path -from [get_ports]` for all I/O | Masks real I/O timing violations | Use false path only for asynchronous control signals (resets, enables) |
| Using wrong period for generated clock reference | Wrong budget for constrained paths | Verify with `report_clocks`; check clock source in `create_generated_clock` |
