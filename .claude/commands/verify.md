# /verify - Verification Workflow

$ARGUMENTS

---

## Purpose

Verify RTL designs with testbenches, assertions, and coverage.

## Setup

Read the following files before creating verification:
- `.agent/agents/verification-engineer.md` for verification methodology
- `.agent/skills/uvm-patterns/SKILL.md` for UVM testbenches
- `.agent/skills/formal-verification/SKILL.md` for assertions
- `.agent/skills/waveform-debugging/SKILL.md` for debug techniques

## Behavior

1. **Analyze DUT**
   - Interfaces
   - Functionality
   - Coverage needs

2. **Create verification**
   - UVM testbench or simple TB (based on complexity)
   - Test sequences
   - Assertions (immediate + concurrent)
   - Functional coverage

3. **Run simulation**
   - Directed tests first
   - Random tests for coverage
   - Check coverage metrics

## UVM Architecture

```
Environment:
├── Agent(s)
│   ├── Sequencer
│   ├── Driver
│   └── Monitor
├── Scoreboard
└── Coverage
```

## Simple Testbench Template

```systemverilog
module tb_dut;
    logic clk = 0;
    always #5 clk = ~clk;

    logic rst_n;

    dut u_dut (
        .clk   (clk),
        .rst_n (rst_n),
        ...
    );

    initial begin
        rst_n = 0;
        #20;
        rst_n = 1;
        // Test cases
        #100;
        $finish;
    end
endmodule
```

## Checklist

- [ ] All DUT interfaces monitored
- [ ] Scoreboard checks all outputs
- [ ] Coverage > 95%
- [ ] Corner cases tested
- [ ] Assertions for protocol compliance
