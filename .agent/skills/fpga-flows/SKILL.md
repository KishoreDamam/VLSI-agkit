---
name: fpga-flows
description: FPGA development flows for Vivado and Quartus.
---

# FPGA Flows

> Development workflows for Xilinx and Intel FPGAs.

---

## Vivado Flow (Xilinx)

### Non-Project Mode (Tcl)

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

### Project Mode (Tcl)

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

## Quartus Flow (Intel)

### Tcl Flow

```tcl
package require ::quartus::project
package require ::quartus::flow

# Create project
project_new my_proj -overwrite - family "Cyclone V"

# Settings
set_global_assignment -name DEVICE 5CSEMA5F31C6
set_global_assignment -name TOP_LEVEL_ENTITY top_module
set_global_assignment -name SYSTEMVERILOG_FILE [glob src/*.sv]
set_global_assignment -name SDC_FILE constraints/timing.sdc

# Compile
execute_flow -compile

# Reports
load_package report
load_report
write_report_panel -file reports/timing.rpt "Timing Analyzer||*"

project_close
```

---

## Common FPGA Patterns

### BRAM Inference

```systemverilog
// Single-port BRAM
(* ram_style = "block" *)
logic [31:0] mem [0:1023];

always_ff @(posedge clk) begin
    if (we)
        mem[addr] <= wdata;
    rdata <= mem[addr];
end
```

### DSP Inference

```systemverilog
// MAC unit using DSP
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

### FIFO with IP

```tcl
# Vivado FIFO IP
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

## Debugging

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

## FPGA-Specific Coding

```systemverilog
// Clock enable instead of clock gating
always_ff @(posedge clk) begin
    if (ce)
        data <= new_data;
end

// Use synchronous reset for FPGA
always_ff @(posedge clk) begin
    if (!rst_n)
        data <= '0;
    else
        data <= new_data;
end
```
