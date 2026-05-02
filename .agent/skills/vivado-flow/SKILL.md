---
name: vivado-flow
description: Use when running Xilinx Vivado from Tcl — project setup, synth_design/place_design/route_design, BRAM/DSP/FIFO inference, ILA/VIO debug insertion, XDC properties, or trimming LUT/BRAM/DSP utilization.
---

# Vivado Flow

> Xilinx Vivado synthesis, implementation, and debug from Tcl.

---

## When to use

- Standing up a Vivado project from Tcl (reproducible build, CI, no GUI dependency).
- Running synth_design / opt_design / place_design / route_design / write_bitstream.
- Inferring BRAM, DSP48, or FIFO from RTL via attributes.
- Inserting ILA/VIO debug cores for in-system observation.
- Trimming LUT/BRAM/DSP usage when fit fails.

**Not for:** Intel Quartus (use `quartus-flow`); ASIC synthesis (use `synopsys-flow` or `cadence-flow`); deep timing-closure methodology (use `timing-constraints` + `synthesis-guidelines`).

---

## Non-Project Mode (Tcl)

```tcl
# Read sources
read_verilog [glob ./src/*.sv]
read_xdc ./constraints/timing.xdc
read_xdc ./constraints/pins.xdc

# Synthesize
synth_design -top top_module -part xc7a100tcsg324-1

# Report utilization
report_utilization -file reports/utilization.rpt

# Optimize, place, route
opt_design
place_design
phys_opt_design
route_design

# Timing report
report_timing_summary -file reports/timing.rpt

# Generate bitstream
write_bitstream -force output/design.bit
```

---

## Project Mode (Tcl)

```tcl
# Create project
create_project my_proj ./my_proj -part xc7a100tcsg324-1

# Add sources
add_files [glob ./src/*.sv]
add_files -fileset constrs_1 ./constraints/timing.xdc
set_property top top_module [current_fileset]

# Run implementation
launch_runs synth_1 -jobs 4
wait_on_run synth_1
launch_runs impl_1 -to_step write_bitstream -jobs 4
wait_on_run impl_1
```

---

## Inference Patterns

### BRAM

```systemverilog
(* ram_style = "block" *)
logic [31:0] mem [0:1023];

always_ff @(posedge clk) begin
    if (we)
        mem[addr] <= wdata;
    rdata <= mem[addr];
end
```

### DSP48

```systemverilog
(* use_dsp = "yes" *)
logic signed [17:0] a, b;
logic signed [47:0] acc;

always_ff @(posedge clk) begin
    if (clear)
        acc <= '0;
    else
        acc <= acc + (a * b);
end
```

### FIFO IP

```tcl
create_ip -name fifo_generator -vendor xilinx.com \
    -library ip -version 13.2 -module_name sync_fifo

set_property -dict [list \
    CONFIG.Fifo_Implementation {Common_Clock_Block_RAM} \
    CONFIG.Input_Data_Width {32} \
    CONFIG.Input_Depth {1024} \
] [get_ips sync_fifo]

generate_target all [get_ips sync_fifo]
```

---

## In-system Debug

### ILA Insertion

```tcl
# Mark nets for debug
set_property MARK_DEBUG true [get_nets {data[*]}]

# Create ILA core
create_debug_core u_ila_0 ila

# Connect probes
set_property port_width 32 [get_debug_ports u_ila_0/probe0]
connect_debug_port u_ila_0/probe0 [get_nets {data[*]}]
```

### VIO for Runtime Control

```tcl
create_debug_core u_vio vio
set_property port_width 8 [get_debug_ports u_vio/probe_out0]
```

---

## Resource Optimization

| Technique | Benefit |
|-----------|---------|
| Use BRAMs | Reduce LUT usage |
| Use DSPs | Fast arithmetic |
| Pack registers | Better routing |
| Floorplan | Timing closure |
| Pipeline | Meet frequency |

---

## FPGA-Specific RTL

```systemverilog
// Clock enable instead of clock gating
always_ff @(posedge clk) begin
    if (ce)
        data <= new_data;
end

// Synchronous reset (preferred on Xilinx flops)
always_ff @(posedge clk) begin
    if (!rst_n)
        data <= '0;
    else
        data <= new_data;
end
```

---

## Anti-patterns (do NOT do this)

1. **Project-mode GUI clicks not captured in Tcl.** Builds become irreproducible; export the Tcl recipe and check it in.
2. **Async reset on Xilinx flops.** Most Xilinx primitives prefer synchronous reset; async reset bloats routing and complicates recovery/removal timing.
3. **Hand-instantiated `RAMB36` / `DSP48E1` primitives.** Hurts portability across families; let synthesis infer from a clean RTL pattern instead.
4. **DSP inference broken by signed/unsigned mismatch.** Use `signed`/`logic signed` consistently or the multiplier maps to LUTs.
5. **`set_property MARK_DEBUG true` left in for production.** Inserts ILA debug nets; clean up before release.
6. **Ignoring fit failures by relaxing constraints.** Fix the design or partition; over-relaxed constraints hide real timing problems.

---

## Validation checklist

- [ ] Project rebuilt from a clean checkout using only the Tcl in the repo (no GUI dependency).
- [ ] Synthesis log: zero critical warnings; latch warnings investigated.
- [ ] Utilization within target (LUT/FF/BRAM/DSP) with margin for ECOs.
- [ ] Timing reports: WNS ≥ 0 for all clock groups (setup) and WHS ≥ 0 (hold).
- [ ] Power estimate within board/thermal budget.
- [ ] Bitstream reproducible: same sources + same Tcl + same Vivado version → same bit-for-bit output.
- [ ] No `MARK_DEBUG` / ILA cores in release bitstream.
