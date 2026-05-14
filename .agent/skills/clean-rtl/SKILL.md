---
name: clean-rtl
description: Use when writing or reviewing any synthesizable Verilog/SystemVerilog — module structure, naming conventions, reset style, port ordering, latch prevention, sequential vs combinational coding rules, or pre-commit RTL self-checks.
---

# Clean RTL - VLSI Coding Standards

> Write RTL that is correct, readable, and synthesizable. The baseline rules every other skill assumes.

---

## When to use

- Writing or reviewing any synthesizable Verilog/SystemVerilog module.
- Setting up the skeleton of a new module (port order, reset style, naming).
- Reviewing a PR and need a checklist of "RTL hygiene" items.
- Lint reports flag latches, naming inconsistencies, or `reg`/`wire` confusion.
- Onboarding someone new to the codebase — point them at this skill first.

**Not for:** module-level architecture decisions (use `brainstorming`); FSM-specific patterns (use `fsm-design`); SystemVerilog feature deep-dives like interfaces/structs (use `systemverilog-coding`); synthesis directives or QoR (use `synthesis-guidelines`).

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

## Anti-patterns (do NOT do this)

1. **`always @(*)` for combinational logic.** Use `always_comb`. The simulator can detect missing assignments and raise warnings; `@(*)` cannot, so latches sneak through.
2. **Blocking assignments (`=`) inside `always_ff`.** Causes simulation/synthesis mismatches because non-blocking is what hardware actually does. Always `<=` in sequential.
3. **Non-blocking (`<=`) inside `always_comb`.** Inverse mistake — `always_comb` models combinational logic which has no concept of "next-cycle"; use `=`.
4. **`reg` keyword in new SystemVerilog code.** Use `logic`. `reg` survives only for legacy compatibility and obscures the actual storage element being inferred.
5. **Magic numbers in widths or comparisons.** Use named `parameter`/`localparam` so the intent is greppable and the value can be overridden.
6. **Implicit net declarations.** Always use `` `default_nettype none `` at the top of each file or rely on lint to catch undeclared identifiers — typos otherwise infer 1-bit wires.
7. **Mixing reset polarities or styles within one module.** Pick async/sync and active-high/low project-wide; mixing creates CDC-style timing issues on the reset tree.
8. **Deep `if/else` chains for state machines.** Use a `case` block (and `unique`/`priority` where appropriate) — synthesis recognizes the pattern and lint can prove full coverage.

---

## Anti-pattern quick reference

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

## Validation checklist (pre-commit)

- [ ] Every register reachable by reset is initialized in the reset branch.
- [ ] No inferred latches: synthesis report shows zero `LATCH` cells; lint shows no `INFERRED_LATCH`.
- [ ] Lint clean against project ruleset (no new warnings or waivers without justification).
- [ ] Naming follows the conventions table above (ports, params, instances, generates).
- [ ] No `reg`/`always @(*)` in new code; `logic` + `always_comb` / `always_ff` only.
- [ ] No magic numbers in widths or comparisons — use `parameter`/`localparam`.
- [ ] `` `default_nettype none `` at file top, or equivalent lint rule enabled.
- [ ] Reset polarity and style consistent with project convention (async vs sync, active-low standard).
- [ ] Inline assertions (`assert`/`$isunknown`) added for protocol-level invariants.
- [ ] Comments explain *why* on non-obvious decisions; module header has Description block.

---

## See also

- `references/simulation-race.md` — read-write / write-write / always-initial races, NBA discipline, Cummings' 8 guidelines.
- `references/sim-synth-mismatch.md` — eight canonical causes of RTL-vs-netlist divergence.
- `references/latch-inference.md` — when latches are inferred, when intentional, `unique`/`priority` traps.
- `references/synchronous-reset.md` — coding idiom that lets synthesis map reset to the flop's sync-clear pin.
- `systemverilog-coding` — `logic` vs `reg` vs `wire`, `always_comb` vs `@*`, struct drivers, generate-for.
- `fsm-design` — state-machine patterns and latch-free `case` discipline.
- `synthesis-guidelines` — synthesis-aware RTL beyond the basics (attributes, retiming, GLS readiness).
