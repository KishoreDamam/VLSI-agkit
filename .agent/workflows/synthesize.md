---
description: Synthesis workflow with constraints and optimization.
---

# /synthesize - Synthesis Workflow

$ARGUMENTS

---

## Purpose

Synthesize RTL to gates with timing closure.

## Resources

- **Lead agent:** `synthesis-engineer`
- **Supporting agents:** `timing-analyst` (when timing fails), `fpga-specialist` or `asic-specialist` depending on target
- **Required skills:** `synthesis-guidelines` (RTL coding for synth), `timing-constraints` (SDC/XDC authoring)
- **Tool flow skills (pick by target):**
  - Xilinx → `vivado-flow`
  - Intel/Altera → `quartus-flow`
  - Synopsys (Design Compiler) → `synopsys-flow`
  - Cadence (Genus) → `cadence-flow`
- **Conditional skills:** `tcl-scripting` (custom build automation), `low-power-design` (clock-gating, multi-Vt), `dft-patterns` (scan insertion)

---

## Behavior

1. **Setup**
   - Target device/library
   - Constraints

2. **Synthesize**
   - Run synthesis tool
   - Check reports

3. **Iterate**
   - Fix violations
   - Optimize

---

## Constraint File (SDC)

```tcl
# Clock
create_clock -period 10.0 [get_ports clk]

# I/O
set_input_delay -clock clk -max 2.0 [all_inputs]
set_output_delay -clock clk -max 2.0 [all_outputs]

# Exceptions
set_false_path -from [get_ports rst_n]
```

---

## Key Reports

| Report | Check For |
|--------|-----------|
| Timing | Positive slack |
| Area | Within budget |
| Power | Acceptable |
| Warnings | No critical |

---

## Checklist

- [ ] All clocks defined
- [ ] I/O delays set
- [ ] Timing met
- [ ] No latch warnings
- [ ] Area OK

---

## Examples

```
/synthesize for Artix-7 at 100MHz
/synthesize with tight area constraints
/synthesize check timing report
```
