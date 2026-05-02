---
name: cadence-flow
description: Use when running Cadence ASIC tools — Genus synthesis, Xcelium simulation, JasperGold formal, or Conformal LEC equivalence checking.
---

# Cadence Flow

> Cadence ASIC front-end tools: Genus, Xcelium, JasperGold, Conformal.

---

## When to use

- Running Genus (`syn_generic` / `syn_map` / `syn_opt`) for ASIC synthesis.
- Compiling and running simulation in Xcelium (`xrun`).
- Property proving in JasperGold.
- Equivalence checking RTL vs. netlist with Conformal.

**Not for:** Synopsys equivalents (use `synopsys-flow`); FPGA flows (use `vivado-flow` / `quartus-flow`); SDC authoring (use `timing-constraints`); RTL coding rules (use `synthesis-guidelines`).

---

## Genus (synthesis)

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
report_area   > rpt/area.rpt
report_power  > rpt/power.rpt

# Output
write_hdl > netlist/top_module.v
write_sdc > out/mapped.sdc
```

---

## Xcelium (simulation)

```bash
# Compile and run
xrun -sv -f filelist.f \
    -timescale 1ns/1ps \
    +define+SIM \
    -access +rwc \
    -input run.tcl
```

---

## JasperGold (formal)

```tcl
# Read design and properties
analyze -sv [glob rtl/*.sv]
analyze -sva assertions.sva
elaborate -top top_module

# Setup clocks/resets
clock clk
reset !rst_n

# Prove
prove -all

# Report
report -summary
```

---

## File Organization

```
project/
├── rtl/              # RTL source
├── tb/               # Testbenches
├── constraints/      # SDC files
├── scripts/
│   ├── syn/          # Genus scripts
│   ├── sim/          # Xcelium scripts
│   └── formal/       # JasperGold scripts
├── work/             # Tool outputs
└── reports/          # Reports
```

---

## Anti-patterns (do NOT do this)

1. **Library setup hardcoded in scripts.** Source from environment so the flow runs at multiple sites/PDKs.
2. **Forgetting `init_design` after `elaborate`.** Genus's internal data model isn't ready until `init_design` runs; downstream commands will silently behave wrong.
3. **Skipping `read_sdc` before `syn_generic`.** No constraints → no timing-driven optimization → garbage QoR.
4. **Mixing Genus and DC scripts in one repo without an abstraction layer.** Use a thin wrapper that dispatches per environment variable.
5. **Lint and CDC reports not gated in CI.** Reports nobody reads = bugs nobody catches.
6. **Hand-edited netlists.** Always re-run synth from RTL; manual netlist edits don't survive the next ECO.

---

## Validation gates

- [ ] `read_hdl` + `elaborate` + `init_design` clean (no unresolved references).
- [ ] Genus WNS ≥ 0 across all clock groups, or every violator documented and waivered.
- [ ] Xcelium regression PASS rate = 100% on the gate-level netlist (GLS sanity).
- [ ] JasperGold proofs converge (proven, not bounded), or boundedness justified.
- [ ] Tool versions and library setup recorded with each release.
