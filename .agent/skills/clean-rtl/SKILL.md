---
name: clean-rtl
description: RTL coding standards, naming conventions, and synthesizable patterns. Core skill for all RTL development.
priority: CRITICAL
---

# Clean RTL - VLSI Coding Standards

> **CRITICAL SKILL** - Write RTL that is correct, readable, and synthesizable.

---

## Naming Conventions

| Element | Convention | Example |
|---------|------------|---------|
| Module | `lowercase_with_underscores` | `fifo_controller` |
| Input port | `i_name` or `name_i` | `i_data`, `valid_i` |
| Output port | `o_name` or `name_o` | `o_data`, `ready_o` |
| Inout port | `io_name` | `io_sda` |
| Clock | `clk` or `clk_<domain>` | `clk`, `clk_100m` |
| Reset | `rst_n` (active low) | `rst_n`, `arst_n` |
| Parameter | `UPPER_CASE` | `DATA_WIDTH` |
| Localparam | `UPPER_CASE` | `STATE_IDLE` |
| Typedef | `name_t` | `state_t`, `cmd_t` |
| Enum value | `UPPER_CASE` | `IDLE`, `ACTIVE` |
| Generate | `gen_<name>` | `gen_pipeline` |
| Instance | `u_<name>` or `i_<name>` | `u_fifo`, `i_arbiter` |

---

## Code Structure

### Module Organization

```systemverilog
//-----------------------------------------------------------------------------
// Module: name
// Description: Brief description
//-----------------------------------------------------------------------------
module module_name #(
    // Parameters
    parameter int DATA_WIDTH = 32
) (
    // Clock and Reset
    input  logic              clk,
    input  logic              rst_n,
    
    // Interface A
    input  logic [7:0]        i_a_data,
    output logic              o_a_ready,
    
    // Interface B
    output logic [7:0]        o_b_data,
    input  logic              i_b_ready
);

    //-------------------------------------------------------------------------
    // Type Definitions
    //-------------------------------------------------------------------------
    
    //-------------------------------------------------------------------------
    // Local Parameters
    //-------------------------------------------------------------------------
    
    //-------------------------------------------------------------------------
    // Signal Declarations
    //-------------------------------------------------------------------------
    
    //-------------------------------------------------------------------------
    // Submodule Instances
    //-------------------------------------------------------------------------
    
    //-------------------------------------------------------------------------
    // Sequential Logic
    //-------------------------------------------------------------------------
    
    //-------------------------------------------------------------------------
    // Combinational Logic
    //-------------------------------------------------------------------------
    
    //-------------------------------------------------------------------------
    // Assertions
    //-------------------------------------------------------------------------

endmodule
```

---

## Sequential Logic Rules

| Rule | Example |
|------|---------|
| Use `always_ff` | `always_ff @(posedge clk)` |
| Non-blocking only | `data <= new_data;` |
| Reset all registers | Include in reset block |
| One clock per block | Don't mix clocks |

```systemverilog
// ✅ Correct
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        data  <= '0;
        valid <= 1'b0;
    end else begin
        data  <= next_data;
        valid <= next_valid;
    end
end
```

---

## Combinational Logic Rules

| Rule | Example |
|------|---------|
| Use `always_comb` | `always_comb begin` |
| Blocking only | `result = a + b;` |
| Assign all outputs | Prevent latches |
| Default first | `out = '0; if...` |

```systemverilog
// ✅ Correct - default assignment
always_comb begin
    next_state = state;  // Default: hold
    case (state)
        IDLE: if (start) next_state = RUN;
        RUN:  if (done)  next_state = IDLE;
    endcase
end
```

---

## Latch Prevention

```systemverilog
// ❌ Creates latch
always_comb begin
    if (sel) out = in1;
    // Missing else creates latch!
end

// ✅ Method 1: Complete conditions
always_comb begin
    if (sel) out = in1;
    else     out = in2;
end

// ✅ Method 2: Default assignment
always_comb begin
    out = '0;  // Default
    if (sel) out = in1;
end

// ✅ Method 3: Case with default
always_comb begin
    case (sel)
        2'b00: out = a;
        2'b01: out = b;
        default: out = '0;
    endcase
end
```

---

## Reset Design

| Type | Use Case | Code |
|------|----------|------|
| Async reset (ASIC) | Power-on reliable | `@(posedge clk or negedge rst_n)` |
| Sync reset (FPGA) | Cleaner timing | `@(posedge clk) if (!rst_n)` |
| Active low | Industry standard | `rst_n` |

---

## Port Ordering

1. Clock(s)
2. Reset(s)
3. Control inputs
4. Data inputs
5. Control outputs
6. Data outputs

---

## Anti-Patterns

| ❌ Don't | ✅ Do |
|----------|-------|
| `always @(*)` | `always_comb` |
| Blocking in sequential | Non-blocking (`<=`) |
| `reg` keyword | `logic` |
| Magic numbers | Named parameters |
| Deep nesting | Flatten with functions |
| Implicit nets | Explicit declarations |

---

## Assertions (Inline)

```systemverilog
// synthesis translate_off
always @(posedge clk) begin
    assert (!$isunknown(valid))
        else $error("X on valid signal");
    
    assert (!(valid && !ready && $rose(start)))
        else $error("Protocol violation");
end
// synthesis translate_on
```

---

## Self-Check Before Commit

- [ ] All signals reset
- [ ] No latches (check synthesis)
- [ ] Lint clean
- [ ] Naming consistent
- [ ] Assertions added
- [ ] Comments on complex logic
