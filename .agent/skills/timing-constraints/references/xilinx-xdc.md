# Xilinx XDC Reference (Ultrascale+)

XDC (Xilinx Design Constraints) is a superset of SDC. All standard SDC commands
(`create_clock`, `set_input_delay`, `set_false_path`, etc.) are valid. This file
covers the Xilinx-specific additions.

---

## Pin and I/O Standard Assignment

Every I/O port that connects to a physical package pin requires both a
`PACKAGE_PIN` and an `IOSTANDARD` property. Omitting either causes a DRC error
in implementation.

```tcl
# Clock input on differential pair
set_property PACKAGE_PIN AK17 [get_ports clk_200_p]
set_property IOSTANDARD  LVDS [get_ports clk_200_p]

# Single-ended 3.3 V logic
set_property PACKAGE_PIN W5   [get_ports usr_btn]
set_property IOSTANDARD  LVCMOS33 [get_ports usr_btn]

# SSTL I/O for DDR interface
set_property PACKAGE_PIN AE14 [get_ports ddr_dq[0]]
set_property IOSTANDARD  SSTL15 [get_ports ddr_dq[0]]
```

**Note:** `PACKAGE_PIN` values are device-specific. Always derive them from the
board schematic and cross-check against the target device's package file in
Vivado's I/O Planning view — never hard-code from a different board.

---

## Drive Strength and Slew Rate

Optional properties that control I/O buffer drive strength and output slew.
Defaults are usually appropriate; set only when signal integrity analysis
requires adjustment.

```tcl
set_property DRIVE      8      [get_ports data_out*]
set_property SLEW       SLOW   [get_ports data_out*]
```

---

## `CLOCK_DEDICATED_ROUTE`

Xilinx global clock routing resources (BUFG, BUFR, MMCM) can only be reached
through clock-capable input pads (CCIO). If a clock signal uses a non-CCIO
pad, Vivado will issue a DRC critical warning and may refuse to implement.

```tcl
# Force the clock net onto the backbone global clock resource
# (use only when the input pad is not clock-capable and you accept
# the routing limitation — adds jitter)
set_property CLOCK_DEDICATED_ROUTE BACKBONE [get_nets clk_ext_buf]

# Disable the dedicated route requirement (last resort; high jitter)
set_property CLOCK_DEDICATED_ROUTE FALSE [get_nets clk_ext_buf]
```

**Preferred solution:** Place clock inputs on CCIO-capable pins (marked in the
device I/O list). Use `CLOCK_DEDICATED_ROUTE BACKBONE` only when board layout
prevents a CCIO assignment and timing closure is still achievable.

---

## `CLOCK_BUFFER_TYPE`

Controls which buffer primitive Vivado inserts for a clock net.

```tcl
# Restrict to BUFG (global clock buffer, lowest skew)
set_property CLOCK_BUFFER_TYPE BUFG [get_nets clk_200_buf]

# Use BUFR (regional, supports divide; local clock region only)
set_property CLOCK_BUFFER_TYPE BUFR [get_nets clk_div_buf]

# Prevent buffer insertion (use only for clocks already manually buffered)
set_property CLOCK_BUFFER_TYPE NONE [get_nets clk_pre_buf]
```

---

## Floorplanning: `create_pblock`

Pblocks constrain placement of a set of cells to a physical region of the device.
Use them to co-locate related logic, reduce routing delay, or isolate reconfigurable
partitions.

```tcl
# Create a pblock and assign a rectangular region on the fabric
create_pblock pblock_dsp_path
add_cells_to_pblock [get_pblocks pblock_dsp_path] \
    [get_cells -hierarchical -filter {NAME =~ u_dsp_chain/*}]
resize_pblock [get_pblocks pblock_dsp_path] \
    -add {SLICE_X20Y100:SLICE_X39Y149}

# Optionally restrict to only the specified sites (contain=true prevents
# cells from being placed outside the pblock)
set_property CONTAIN_ROUTING 1 [get_pblocks pblock_dsp_path]
```

**Validation:** After implementation, run `report_utilization -pblocks` and
`report_route_status` to verify all assigned cells are inside the pblock and
routes do not escape the region unnecessarily.

---

## `PROHIBIT` — Excluding Sites

Use `PROHIBIT` to prevent Vivado from placing cells on specific sites.
Common use: reserving sites for future IP, PCB-constrained hard macros, or
sites with known SI issues.

```tcl
# Prohibit a range of BRAMs from general placement
set_property PROHIBIT 1 [get_sites RAMB36_X2Y10:RAMB36_X2Y15]

# Prohibit a DSP site
set_property PROHIBIT 1 [get_sites DSP48E2_X3Y10]
```

---

## I/O Delay Groups (Advanced)

For source-synchronous interfaces sharing a board-level strobe, group related
I/O ports into an `IODELAY_GROUP` so the tool applies a consistent delay
calibration reference.

```tcl
set_property IODELAY_GROUP ddr3_grp0 [get_cells u_phy/idelay_dq*]
set_property IODELAY_GROUP ddr3_grp0 [get_cells u_phy/idelayctrl0]
```

---

## XDC Evaluation Order

Vivado evaluates XDC files in the order they are added to the project. For
in-context runs, SDC constraints from IP customization may be processed before
user XDC files. Use `read_xdc -unmanaged` (in Tcl mode) to control order
explicitly.

---

## Common DRC Errors and Fixes

| DRC Check | Symptom | Fix |
|---|---|---|
| `UCIO-1` | Unplaced I/O; missing `PACKAGE_PIN` | Add `set_property PACKAGE_PIN` for every top-level port |
| `NSTD-1` | Missing `IOSTANDARD` | Add `set_property IOSTANDARD` for every placed port |
| `PDRC-203` | Clock on non-CCIO pin | Move clock to CCIO pin or add `CLOCK_DEDICATED_ROUTE BACKBONE` |
| `PLCK-14` | BUFG driven by non-clock net | Check `CLOCK_BUFFER_TYPE`; or route clock through IBUF first |
