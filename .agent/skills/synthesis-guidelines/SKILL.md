---
name: synthesis-guidelines
description: Synthesis-friendly RTL coding and optimization techniques.
---

# Synthesis Guidelines

> Write RTL that synthesizes efficiently.

---

## Synthesis-Friendly Coding

### Clock and Reset

```systemverilog
// ✅ Recommended: Single clock edge
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        data <= '0;
    else
        data <= new_data;
end

// ❌ Avoid: Dual edge (not all targets support)
always_ff @(posedge clk or negedge clk) // Don't do this
```

### Latch Avoidance

```systemverilog
// ❌ Infers latch
always_comb begin
    if (sel)
        out = a;
    // Missing else!
end

// ✅ Complete assignment
always_comb begin
    out = '0;  // Default
    if (sel)
        out = a;
end
```

---

## Resource Sharing

### Multiplier Sharing

```systemverilog
// Tool can share one multiplier
always_ff @(posedge clk) begin
    if (sel)
        result <= a * b;
    else
        result <= c * d;
end
```

### Adder Tree

```systemverilog
// Let tool optimize the tree
wire [31:0] sum = a + b + c + d + e + f + g + h;
```

---

## Timing Optimization

### Register Outputs

```systemverilog
// ❌ Long comb path to output
assign data_out = complex_logic(data_in);

// ✅ Registered output
always_ff @(posedge clk) begin
    data_out <= complex_logic(data_in);
end
```

### Pipeline Long Paths

```systemverilog
// ❌ Single cycle, may fail timing
assign result = (a * b) + (c * d) + (e * f);

// ✅ Pipelined
always_ff @(posedge clk) begin
    // Stage 1: Multiply
    prod1 <= a * b;
    prod2 <= c * d;
    prod3 <= e * f;
end
always_ff @(posedge clk) begin
    // Stage 2: Add
    result <= prod1 + prod2 + prod3;
end
```

---

## Area Optimization

### Bit Width

```systemverilog
// Use minimum width
localparam COUNTER_WIDTH = $clog2(MAX_COUNT + 1);
logic [COUNTER_WIDTH-1:0] counter;
```

### Mux vs Decoder

```systemverilog
// Mux: Fewer gates for few inputs
assign out = sel ? a : b;

// Decoder: Better for many outputs
always_comb begin
    case (sel)
        2'b00: out = a;
        2'b01: out = b;
        2'b10: out = c;
        2'b11: out = d;
    endcase
end
```

---

## Common Issues

| Issue | Cause | Fix |
|-------|-------|-----|
| Latch | Incomplete if/case | Default assignment |
| Multi-driven | Multiple always | Single driver |
| Combo loop | Feedback path | Add register |
| Undriven | Missing connection | Connect or tie |

---

## Synthesis Directives

```systemverilog
// Preserve hierarchy
(* keep_hierarchy = "yes" *)
module important_block (...);

// Use specific resource
(* use_dsp = "yes" *)
logic signed [17:0] product = a * b;

// RAM style
(* ram_style = "block" *)
logic [31:0] mem [1023:0];

// Don't touch
(* dont_touch = "true" *)
logic critical_signal;
```

---

## Timing Waiver

When timing cannot be met:
1. First try design changes (pipeline)
2. Document why exception is safe
3. Add proper multicycle/false path

```tcl
# Document the reason
# This path is only sampled once per frame
set_multicycle_path 2 -setup -from [get_cells cfg_*]
```
