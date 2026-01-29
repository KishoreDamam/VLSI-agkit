---
name: timing-constraints
description: SDC/XDC timing constraints for synthesis and implementation.
---

# Timing Constraints

> SDC (Synopsys Design Constraints) for timing closure.

---

## Clock Constraints

### Primary Clocks

```tcl
# Simple clock
create_clock -name clk -period 10.0 [get_ports clk]

# Clock with duty cycle
create_clock -name clk -period 10.0 \
    -waveform {0 5} [get_ports clk]
```

### Generated Clocks

```tcl
# Divided clock
create_generated_clock -name clk_div2 \
    -source [get_ports clk] \
    -divide_by 2 \
    [get_pins clk_div/Q]

# Multiplied clock (PLL output)
create_generated_clock -name clk_2x \
    -source [get_pins pll/CLKIN] \
    -multiply_by 2 \
    [get_pins pll/CLKOUT]
```

---

## I/O Constraints

### Input Delay

```tcl
# Set input delay relative to clock
set_input_delay -clock clk -max 2.0 [get_ports data_in*]
set_input_delay -clock clk -min 0.5 [get_ports data_in*]

# DDR input (both edges)
set_input_delay -clock clk_ddr -max 1.0 \
    [get_ports ddr_data*] -clock_fall -add_delay
```

### Output Delay

```tcl
# Set output delay
set_output_delay -clock clk -max 3.0 [get_ports data_out*]
set_output_delay -clock clk -min 0.5 [get_ports data_out*]
```

---

## Clock Groups

### Asynchronous Clocks

```tcl
# No timing analysis between these clocks
set_clock_groups -asynchronous \
    -group [get_clocks clk_a] \
    -group [get_clocks clk_b]
```

### Exclusive Clocks

```tcl
# Clocks never active together (mux)
set_clock_groups -exclusive \
    -group [get_clocks clk_sel0] \
    -group [get_clocks clk_sel1]
```

---

## Path Exceptions

### False Paths

```tcl
# Async reset - no timing
set_false_path -from [get_ports rst_n]

# Static configuration
set_false_path -from [get_cells cfg_reg*]

# Between clock domains (if using synchronizers)
set_false_path -from [get_clocks clk_a] -to [get_clocks clk_b]
```

### Multicycle Paths

```tcl
# 2-cycle setup path
set_multicycle_path 2 -setup \
    -from [get_cells slow_*] -to [get_cells result_*]

# 1-cycle hold (standard adjustment)
set_multicycle_path 1 -hold \
    -from [get_cells slow_*] -to [get_cells result_*]
```

### Max/Min Delay

```tcl
# Maximum delay constraint
set_max_delay 5.0 -from [get_ports async_in] \
    -to [get_cells sync_reg/D]

# Minimum delay constraint
set_min_delay 1.0 -from [get_cells reg1/Q] \
    -to [get_cells reg2/D]
```

---

## Common Patterns

### CDC Synchronizer

```tcl
# 2-FF synchronizer - set max delay
set_max_delay -from [get_cells src_reg] \
    -to [get_cells sync_reg1] \
    -datapath_only [get_property PERIOD [get_clocks dst_clk]]
```

### Reset Synchronizer

```tcl
# Async reset, sync deassert
set_false_path -to [get_cells rst_sync_reg1/D]
```

---

## XDC (Xilinx) Additions

### Pin Constraints

```tcl
set_property PACKAGE_PIN W5 [get_ports clk]
set_property IOSTANDARD LVCMOS33 [get_ports clk]
```

### Clock Properties

```tcl
set_property CLOCK_DEDICATED_ROUTE BACKBONE [get_nets clk]
```

---

## Best Practices

| Practice | Reason |
|----------|--------|
| Constrain all clocks | No unconstrained paths |
| Use clock groups | CDC analysis |
| Document exceptions | Maintainability |
| Minimize false paths | Better coverage |
| Review timing reports | Verify constraints |
