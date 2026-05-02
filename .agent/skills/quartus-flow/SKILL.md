---
name: quartus-flow
description: Use when running Intel/Altera Quartus from Tcl — project creation, global assignments, execute_flow compilation, M10K/M20K memory inference, DSP block inference, or report extraction.
---

# Quartus Flow

> Intel/Altera Quartus synthesis, place & route, and report extraction from Tcl.

---

## When to use

- Standing up a Quartus project from Tcl (reproducible build, CI).
- Running the full compile flow via `execute_flow -compile`.
- Choosing global assignments (device, top entity, file lists, SDC).
- Inferring M10K/M20K block RAM or DSP blocks.
- Extracting timing/area/power reports for downstream gating.

**Not for:** Xilinx Vivado (use `vivado-flow`); ASIC synthesis (use `synopsys-flow` or `cadence-flow`); deep timing-closure methodology (use `timing-constraints` + `synthesis-guidelines`).

---

## Tcl Flow

```tcl
package require ::quartus::project
package require ::quartus::flow

# Create project
project_new my_proj -overwrite -family "Cyclone V"

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

## Inference Patterns

### M10K / M20K BRAM

```systemverilog
(* ramstyle = "M20K" *)
logic [31:0] mem [0:1023];

always_ff @(posedge clk) begin
    if (we)
        mem[addr] <= wdata;
    rdata <= mem[addr];
end
```

### DSP Block

```systemverilog
(* multstyle = "dsp" *)
logic signed [17:0] a, b;
logic signed [35:0] product;

always_ff @(posedge clk)
    product <= a * b;
```

---

## FPGA-Specific RTL

```systemverilog
// Synchronous reset preferred on Cyclone/Stratix flops
always_ff @(posedge clk) begin
    if (!rst_n)
        data <= '0;
    else if (ce)
        data <= new_data;
end
```

---

## Anti-patterns (do NOT do this)

1. **GUI-only project setup.** No Tcl recipe = irreproducible build. Use `project_new` + `set_global_assignment` and check the script in.
2. **Forgetting `project_close`.** Leaves the QPF locked; subsequent builds fail with cryptic errors.
3. **Hand-instantiated `altera_syncram` primitives.** Hurts portability across Cyclone/Stratix families; let synthesis infer from a clean pattern.
4. **`ramstyle` / `multstyle` set on the wrong signal.** The attribute must annotate the storage variable (the array, not the address).
5. **Async reset on Cyclone/Stratix flops.** Quartus prefers synchronous reset; async bloats routing and complicates STA recovery/removal.
6. **Ignoring critical warnings.** Quartus often turns silent design issues into critical warnings; treat them as errors in CI.

---

## Validation checklist

- [ ] Project rebuilt from a clean checkout using only the Tcl in the repo.
- [ ] `execute_flow -compile` completes with zero critical warnings.
- [ ] Utilization (ALMs, M10K/M20K, DSP) within target with ECO margin.
- [ ] TimeQuest timing report: setup and hold met across all corners.
- [ ] Power estimate within board/thermal budget.
- [ ] `.sof` reproducible from a clean checkout with the same Quartus version.
