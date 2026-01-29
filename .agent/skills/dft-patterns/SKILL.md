---
name: dft-patterns
description: Design-for-Test patterns including scan, BIST, and ATPG.
---

# DFT Patterns

> Design-for-Test techniques for manufacturing test.

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
