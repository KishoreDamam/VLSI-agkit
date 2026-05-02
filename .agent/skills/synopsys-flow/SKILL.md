---
name: synopsys-flow
description: Use when running Synopsys ASIC tools — Design Compiler synthesis, VCS simulation, SpyGlass lint/CDC, DFT Compiler scan insertion, or VC Formal property proving.
---

# Synopsys Flow

> Synopsys ASIC front-end tools: DC, VCS, SpyGlass, DFT Compiler, VC Formal.

---

## When to use

- Running Design Compiler (`compile_ultra`) for ASIC synthesis.
- Compiling and running simulation in VCS.
- SpyGlass lint, CDC, or low-power rule checking.
- Inserting scan chains with DFT Compiler (`insert_dft`).
- Property proving in VC Formal.

**Not for:** Cadence equivalents (use `cadence-flow`); FPGA flows (use `vivado-flow` / `quartus-flow`); SDC/XDC authoring (use `timing-constraints`); RTL coding rules (use `synthesis-guidelines`).

---

## Design Compiler (synthesis)

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
report_area   > rpt/area.rpt
report_power  > rpt/power.rpt
report_qor    > rpt/qor.rpt

# Output
write -format verilog -hierarchy -output netlist/${TOP}.v
write_sdc out/${TOP}.sdc
write_sdf out/${TOP}.sdf
```

---

## VCS (simulation)

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

---

## SpyGlass (lint + CDC)

```tcl
# Project setup
new_project lint_proj
read_file -type verilog [glob rtl/*.sv]
set_option top top_module

# Lint
current_goal lint/lint_rtl
run_goal
write_report lint_report.rpt

# CDC
current_goal cdc/cdc_verify
run_goal
write_report cdc_report.rpt
```

---

## DFT Compiler (scan insertion)

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

## VC Formal (property proof)

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
│   ├── syn/          # DC scripts
│   ├── sim/          # VCS scripts
│   ├── lint/         # SpyGlass scripts
│   ├── dft/          # DFT Compiler scripts
│   └── formal/       # VC Formal scripts
├── work/             # Tool outputs
└── reports/          # Reports
```

---

## Anti-patterns (do NOT do this)

1. **Library setup hardcoded in scripts.** Source a `setup.tcl` from environment so the same flow runs at multiple sites/PDKs.
2. **Skipping `link` / `check_design` after `analyze` + `elaborate`.** Unresolved references and partial elaboration silently produce wrong netlists.
3. **Running `compile_ultra` without an SDC.** DC defaults to no clock → trivially-met timing → garbage QoR.
4. **Lint and CDC reports not gated in CI.** Reports nobody reads = bugs nobody catches.
5. **Hand-edited netlists.** Always re-run synth from RTL; manual netlist edits don't survive the next ECO.
6. **`compile` instead of `compile_ultra`.** Legacy command — `compile_ultra` is the modern flow with better timing closure.

---

## Validation gates

- [ ] `analyze` + `elaborate` + `link` clean (no unresolved references).
- [ ] `check_design` reports zero blocking errors.
- [ ] DC WNS ≥ 0 across all clock groups, or every violator documented and waivered.
- [ ] SpyGlass lint + CDC waiver lists reviewed; no new unwaived violations.
- [ ] VCS regression PASS rate = 100% on the gate-level netlist (GLS sanity).
- [ ] DFT Compiler stuck-at coverage ≥ 99% (or project target).
- [ ] VC Formal proofs all converge (proven, not bounded), or boundedness justified.
- [ ] Tool versions and library setup recorded with each release.
