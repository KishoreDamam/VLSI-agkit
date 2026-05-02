---
name: dft-patterns
description: Use when inserting scan chains, MBIST, or LBIST, writing JTAG/TAP-controller logic, evaluating ATPG coverage, or fixing DFT rule violations on non-scannable structures (latches, gated clocks, async reset).
---

# DFT Patterns

> Design-for-Test techniques for manufacturing test.

---

## When to use

- Targeting an ASIC where manufacturing test coverage is a sign-off requirement.
- Inserting scan chains, MBIST/LBIST controllers, or JTAG/TAP logic.
- Reviewing RTL for DFT rule violations (latches, gated clocks, async resets without test mux).
- Hitting low ATPG coverage and need to identify untestable structures.
- Wrapping reusable IP with scan boundaries (IEEE 1500).

**Not for:** FPGA designs (no manufacturing test); pre-RTL exploration (DFT decisions come after architecture is stable).

---

## DFT Overview

| Technique | Purpose |
|-----------|---------|
| Scan | Test sequential logic |
| BIST | Self-test (memory, logic) |
| JTAG | Boundary scan |
| ATPG | Generate test patterns |

---

## Scan Design

### Scannable Flip-Flop

```systemverilog
// Tool replaces with scan FF
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        data <= '0;
    else
        data <= d_in;
end

// Becomes (conceptually):
// MUX: scan_en ? scan_in : d_in
```

### Non-Scannable Structures

| Structure | Issue | Solution |
|-----------|-------|----------|
| Async reset | Scan conflict | Reset during scan |
| Gated clock | Scan clock | Bypass during test |
| Latches | Timing | Avoid or isolate |

---

## BIST

### Memory BIST

```systemverilog
module mbist #(
    parameter int DEPTH = 1024,
    parameter int WIDTH = 32
) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic         bist_en,
    output logic         bist_done,
    output logic         bist_fail,
    
    // Memory interface
    output logic         mem_we,
    output logic [$clog2(DEPTH)-1:0] mem_addr,
    output logic [WIDTH-1:0] mem_wdata,
    input  logic [WIDTH-1:0] mem_rdata
);
    // March C- algorithm
    typedef enum {
        IDLE,
        WRITE_0,  // Write 0 to all
        READ_0_WRITE_1,  // Read 0, write 1 (ascending)
        READ_1_WRITE_0,  // Read 1, write 0 (ascending)
        READ_0_2,  // Read 0 (descending)
        DONE
    } state_t;
endmodule
```

### Logic BIST

```systemverilog
// LFSR for pattern generation
module lfsr #(parameter WIDTH = 16) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic             enable,
    output logic [WIDTH-1:0] pattern
);
    // Example: x^16 + x^14 + x^13 + x^11 + 1
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            pattern <= 16'hACE1;  // Seed
        else if (enable)
            pattern <= {pattern[14:0], 
                       pattern[15] ^ pattern[13] ^ 
                       pattern[12] ^ pattern[10]};
    end
endmodule
```

---

## JTAG (IEEE 1149.1)

### TAP Controller States

```
Test-Logic-Reset
      ↓
Run-Test/Idle ←→ [DR path] ←→ [IR path]
```

### Mandatory Registers

| Register | Code | Purpose |
|----------|------|---------|
| BYPASS | All 1s | Skip device |
| IDCODE | Vendor | Identify device |
| EXTEST | User | External test |
| SAMPLE | User | Sample pins |

---

## DFT Rules

| Rule | Reason |
|------|--------|
| Reset controllable | Enter scan mode |
| Clocks controllable | Scan shifting |
| No combinational feedback | ATPG |
| Observe/control key points | Coverage |

---

## ATPG Coverage

| Fault Model | Description |
|-------------|-------------|
| Stuck-at | Node stuck at 0 or 1 |
| Transition | Slow-to-rise/fall |
| Path delay | Timing faults |
| Bridge | Unintended shorts |

---

## DFT Insertion Flow

```tcl
# DFT Compiler
set_scan_configuration -chain_count 4
create_test_protocol
dft_drc
insert_dft

report_scan_path
write_test_protocol test.spf
```

---

## Anti-patterns (do NOT do this)

1. **Latches in the design without a test bypass.** Transparent latches break scan and ATPG; either remove them (almost always the right answer) or wrap with a test mux.
2. **Gated clocks without test enable.** Clock gates must observe `test_en` (or use a `CKLNQD` ICG with `TE`); otherwise scan shifts don't reach gated registers.
3. **Async resets driven by combinational logic.** Async-reset DRC requires a mux on the reset path so test mode pulls a clean value.
4. **Black-box memories without MBIST.** Embedded SRAMs need MBIST; otherwise no manufacturing fault coverage on the array.
5. **Sharing scan chains across power domains without isolation.** Shifting through a powered-down domain corrupts the chain.
6. **Reporting ATPG coverage on stuck-at only.** Modern flows require transition-fault and at-speed coverage too.

---

## Validation checklist

- [ ] No transparent latches in the design (lint clean) or all latches scan-isolated.
- [ ] All clock gates have `test_en` observability; verified by DFT DRC.
- [ ] Async resets bypassed in scan/test mode.
- [ ] Stuck-at ATPG coverage ≥ 99%, transition ≥ project target.
- [ ] MBIST inserted on every embedded memory; BIST controller verified in simulation.
- [ ] JTAG TAP passes IEEE 1149.1 boundary scan compliance test.
- [ ] Scan chains balanced (length within tool tolerance) and routed across power domains correctly.
- [ ] Test patterns regenerated and re-verified after final ECO.
