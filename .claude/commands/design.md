# /design - RTL Design Workflow

$ARGUMENTS

---

## Purpose

Design RTL modules following best practices.

## Setup

Read the following files before designing:
- `.agent/agents/rtl-designer.md` for design methodology
- `.agent/skills/clean-rtl/SKILL.md` for coding standards (MANDATORY)
- `.agent/skills/systemverilog-patterns/SKILL.md` for SV patterns
- `.agent/skills/fsm-design/SKILL.md` if FSMs are involved

For target-specific guidance, also read:
- `.agent/agents/fpga-specialist.md` and `.agent/skills/fpga-flows/SKILL.md` for FPGA targets
- `.agent/agents/asic-specialist.md` and `.agent/skills/asic-flows/SKILL.md` for ASIC targets

## Behavior

1. **Clarify requirements**
   - Interface (protocol, widths)
   - Timing (clock, latency)
   - Target (FPGA/ASIC)

2. **Create RTL**
   - Follow `clean-rtl` skill naming and structure rules
   - Use module template below
   - Add inline assertions

3. **Lint check**
   - Verify no latches inferred
   - Check width mismatches
   - Confirm all signals reset

## Module Template

```systemverilog
//-----------------------------------------------------------------------------
// Module: name
// Description: Brief description
//-----------------------------------------------------------------------------
module module_name #(
    parameter int DATA_WIDTH = 32
) (
    // Clock and Reset
    input  logic                    clk,
    input  logic                    rst_n,

    // Interface
    input  logic [DATA_WIDTH-1:0]   i_data,
    output logic [DATA_WIDTH-1:0]   o_data
);

    // Type Definitions
    // Internal Signals
    // Sequential Logic (always_ff, non-blocking <=)
    // Combinational Logic (always_comb, blocking =)
    // Assertions

endmodule
```

## Checklist

- [ ] Parameterized widths
- [ ] All signals reset in always_ff blocks
- [ ] No latches (complete if/else, default in case)
- [ ] Assertions added for critical paths
- [ ] Lint clean
