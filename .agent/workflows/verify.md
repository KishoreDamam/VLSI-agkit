---
description: Verification workflow including UVM and simulation.
---

# /verify - Verification Workflow

$ARGUMENTS

---

## Purpose

Verify RTL designs with testbenches and coverage.

## Resources

- **Lead agent:** `verification-engineer`
- **Supporting agents:** `debugger` (when failures emerge), `rtl-designer` (testbench-driven RTL fixes)
- **Required skills:** `uvm-coding` (for full UVM TBs), `formal-verification` (assertions/properties)
- **Conditional skills:** `axi-protocols` (protocol-compliance suites), `clock-domain-crossing` (multi-clock TBs), `waveform-debugging` (when failures need root-causing)

---

## Behavior

1. **Analyze DUT**
   - Interfaces
   - Functionality
   - Coverage needs

2. **Create verification**
   - UVM testbench or simple TB
   - Test sequences
   - Assertions
   - Coverage

3. **Run simulation**
   - Directed tests
   - Random tests
   - Check coverage

---

## UVM Components

```
Agent:
├── Sequencer
├── Driver  
└── Monitor

Environment:
├── Agent(s)
├── Scoreboard
└── Coverage
```

---

## Simple Testbench

```systemverilog
module tb_dut;
    logic clk = 0;
    always #5 clk = ~clk;
    
    dut u_dut (.clk(clk), ...);
    
    initial begin
        // Test cases
        $finish;
    end
endmodule
```

---

## Checklist

- [ ] All interfaces monitored
- [ ] Scoreboard checks outputs
- [ ] Coverage > 95%
- [ ] Corner cases tested

---

## Examples

```
/verify FIFO with UVM
/verify counter with simple TB
/verify AXI protocol compliance
```
