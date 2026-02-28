# /synthesize - Synthesis Workflow

$ARGUMENTS

---

## Purpose

Synthesize RTL to gates with timing closure.

## Setup

Read the following files for synthesis guidance:
- `.agent/agents/synthesis-engineer.md` for synthesis methodology
- `.agent/skills/synthesis-guidelines/SKILL.md` for synth-friendly coding
- `.agent/skills/timing-constraints/SKILL.md` for SDC/XDC constraints

For target-specific flows:
- `.agent/skills/fpga-flows/SKILL.md` for Vivado/Quartus
- `.agent/skills/asic-flows/SKILL.md` for Synopsys DC/Cadence Genus

## Behavior

1. **Setup**
   - Identify target device/library
   - Create or review constraints

2. **Synthesize**
   - Run synthesis tool
   - Check reports (timing, area, power)

3. **Iterate**
   - Fix timing violations
   - Optimize area/power

## Constraint File Template (SDC)

```tcl
# Clock
create_clock -period 10.0 [get_ports clk]

# I/O Delays
set_input_delay -clock clk -max 2.0 [all_inputs]
set_output_delay -clock clk -max 2.0 [all_outputs]

# Exceptions
set_false_path -from [get_ports rst_n]
```

## Key Reports

| Report | Check For |
|---|---|
| Timing | Positive slack (WNS > 0) |
| Area | Within budget |
| Power | Acceptable levels |
| Warnings | No critical warnings |

## Checklist

- [ ] All clocks defined
- [ ] I/O delays set
- [ ] Timing met (WNS > 0, TNS = 0)
- [ ] No latch warnings
- [ ] Area within budget
