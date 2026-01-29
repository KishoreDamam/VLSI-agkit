---
description: RTL design workflow with templates and best practices.
---

# /design - RTL Design Workflow

$ARGUMENTS

---

## Purpose

Design RTL modules following best practices.

---

## Behavior

1. **Clarify requirements**
   - Interface (protocol, widths)
   - Timing (clock, latency)
   - Target (FPGA/ASIC)

2. **Create RTL**
   - Follow `clean-rtl` skill
   - Use module template
   - Add assertions

3. **Lint check**
   - Run lint before completion

---

## Module Template

```systemverilog
module name #(
    parameter int DATA_WIDTH = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [DATA_WIDTH-1:0] i_data,
    output logic [DATA_WIDTH-1:0] o_data
);
    // Implementation
endmodule
```

---

## Checklist

- [ ] Parameterized
- [ ] All signals reset
- [ ] No latches
- [ ] Assertions added
- [ ] Lint clean

---

## Examples

```
/design synchronous FIFO
/design AXI-Lite slave
/design 4-bit counter with enable
```
