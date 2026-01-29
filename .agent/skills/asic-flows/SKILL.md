---
name: asic-flows
description: ASIC development flows for Synopsys and Cadence tools.
---

# ASIC Flows

> Development workflows for ASIC front-end.

---

## Synthesis Flow

### Design Compiler (Synopsys)

```tcl
# Setup
set TOP my_design
set TECH_LIB /libs/tech.db
set TARGET_LIB /libs/std_cell.db

set link_library "* $TECH_LIB $TARGET_LIB"
set target_library $TARGET_LIB

# Read RTL
analyze -format sverilog [glob rtl/*.sv]
elaborate $TOP
link

# Constraints
source constraints/timing.sdc

# Compile
compile_ultra -timing_high_effort_script

# Reports
report_timing > rpt/timing.rpt
report_area > rpt/area.rpt
report_power > rpt/power.rpt
report_qor > rpt/qor.rpt

# Output
write -format verilog -hierarchy -output netlist/${TOP}.v
write_sdc out/${TOP}.sdc
write_sdf out/${TOP}.sdf
```

### Genus (Cadence)

```tcl
# Setup
set_db init_lib_search_path /libs
set_db library {std_cell.lib}

# Read design
read_hdl -sv [glob rtl/*.sv]
elaborate top_module
init_design

# Constraints
read_sdc constraints/timing.sdc

# Synthesize
syn_generic
syn_map
syn_opt

# Reports
report_timing > rpt/timing.rpt
report_area > rpt/area.rpt

# Output
write_hdl > netlist/top_module.v
write_sdc > out/mapped.sdc
```

---

## Simulation Flow

### VCS (Synopsys)

```bash
# Compile
vcs -full64 -sverilog \
    -f filelist.f \
    -timescale=1ns/1ps \
    +define+SIM \
    -o simv

# Run
./simv +fsdbDumpfile=dump.fsdb
```

### Xcelium (Cadence)

```bash
# Compile and run
xrun -sv -f filelist.f \
    -timescale 1ns/1ps \
    +define+SIM \
    -access +rwc \
    -input run.tcl
```

---

## Lint Flow

### SpyGlass (Synopsys)

```tcl
# Project setup
new_project lint_proj
read_file -type verilog [glob rtl/*.sv]
set_option top top_module

# Run lint
current_goal lint/lint_rtl
run_goal

# Reports
write_report lint_report.rpt
```

### Verilator

```bash
verilator --lint-only -Wall \
    -Wno-UNUSED -Wno-PINCONNECTEMPTY \
    -f filelist.f
```

---

## CDC Analysis

```tcl
# SpyGlass CDC
current_goal cdc/cdc_verify
run_goal

# Report violations
write_report cdc_report.rpt
```

---

## DFT Flow

### DFT Compiler (Synopsys)

```tcl
# Pre-DFT
set_scan_configuration -chain_count 4
set_scan_configuration -clock_mixing no_mix

# Check DFT rules
create_test_protocol
dft_drc

# Insert scan
insert_dft
write -format verilog -output scan_netlist.v

# Report
report_scan_path > scan_path.rpt
```

---

## Verification

### Formal (VC Formal)

```tcl
# Setup
read_file -type verilog netlist/design.v
read_file -type sva assertions.sva

# Run formal
set_engine_mode {Hp Ht}
prove -all

# Report
report_property -all
```

---

## File Organization

```
project/
├── rtl/              # RTL source
├── tb/               # Testbenches
├── constraints/      # SDC files
├── scripts/
│   ├── syn/          # Synthesis scripts
│   ├── sim/          # Simulation scripts
│   └── dft/          # DFT scripts
├── work/             # Tool outputs
└── reports/          # Reports
```
