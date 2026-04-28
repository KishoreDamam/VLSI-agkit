# Synthesis Attributes Reference

> Comprehensive reference for synthesis pragmas and attributes in Vivado (Xilinx/AMD) and Design Compiler / Genus (Synopsys/Cadence). Attributes control resource inference, optimization boundaries, and net preservation.

---

## Portability Warning

Synthesis attributes embedded in RTL are **tool-specific and non-portable**. An attribute that is valid for Vivado is silently ignored (or causes a warning) in DC, and vice versa.

Best practice: wrap tool-specific attributes in `` `ifdef SYNTHESIS `` or in a parameter file, so a simulation-only flow does not need to parse them.

```systemverilog
`ifdef SYNTHESIS
(* use_dsp = "yes" *)
`endif
logic signed [31:0] product;
assign product = $signed(a) * $signed(b);
```

---

## Full Attribute Table

### Net and Cell Preservation

| Attribute / Command | Tool | Syntax location | Effect |
|---|---|---|---|
| `(* keep = "true" *)` | Vivado | Before `logic` declaration | Preserves the net name through optimization; the logic driving it may still be optimized |
| `(* dont_touch = "true" *)` | Vivado | Before `logic` or `module` | Prevents the cell and its driving net from being optimized, merged, or removed |
| `set_dont_touch [get_cells <name>]` | DC, Genus | TCL constraint file | Freezes named cell from all optimization passes |
| `set_dont_touch [get_nets <name>]` | DC, Genus | TCL constraint file | Preserves net from being merged or optimized away |

**When to use `dont_touch`:** debug observation points (probe registers), clock gating cells you want to control manually, or any register that synthesis correctly infers but then removes as "redundant".

### DSP Inference Control

| Attribute / Command | Tool | Value | Effect |
|---|---|---|---|
| `(* use_dsp = "yes" *)` | Vivado | `"yes"` | Forces multiply (or multiply-accumulate) to DSP48E2/DSP58 block |
| `(* use_dsp = "no" *)` | Vivado | `"no"` | Prevents DSP inference; uses LUTs instead |
| `set_use_dsp true` | DC | TCL | Enables DSP mapping for the current module or net |
| `set_use_dsp false` | DC | TCL | Disables DSP mapping |

**Notes:**
- Vivado requires the attribute on the **output** register or wire of the multiply, not on the operands.
- For DC, `set_use_dsp` is a compile directive; apply it before `compile_ultra`.
- Using `$signed(a) * $signed(b)` helps the tool recognize signed multiplies for DSP inference even without the attribute.

```systemverilog
// Force DSP for this multiply-accumulate
(* use_dsp = "yes" *)
logic signed [47:0] accum;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) accum <= '0;
    else        accum <= accum + $signed(a) * $signed(b);
end
```

### RAM Inference Control

| Attribute / Command | Tool | Value | Effect |
|---|---|---|---|
| `(* ram_style = "block" *)` | Vivado | `"block"` | Forces BRAM (Block RAM) inference |
| `(* ram_style = "distributed" *)` | Vivado | `"distributed"` | Forces LUT RAM (distributed) inference |
| `(* ram_style = "registers" *)` | Vivado | `"registers"` | Forces register array (FF-based) — no BRAM, no LUT RAM |
| `(* ram_style = "ultra" *)` | Vivado (UltraScale+) | `"ultra"` | Forces UltraRAM (URAM) inference |

**Placement:** attribute goes immediately before the array declaration.

```systemverilog
// Force 8 KB BRAM
(* ram_style = "block" *)
logic [31:0] mem [2047:0];

always_ff @(posedge clk) begin
    if (we) mem[waddr] <= wdata;
    rdata <= mem[raddr];
end
```

**DC equivalent:** DC infers RAMs based on coding style. Use `set_attribute [get_references <module>] map_to_entity "ram"` or the memory compiler flow. DC does not use the `ram_style` Vivado attribute.

### Hierarchy Preservation

| Attribute / Command | Tool | Effect |
|---|---|---|
| `(* keep_hierarchy = "yes" *)` | Vivado | Prevents boundary optimization across the module boundary; timing analysis reflects the module's internal paths |
| `set_boundary_optimization false [get_designs <module>]` | DC | Preserves module boundaries during optimization |
| `set_dont_touch [get_designs <module>]` | DC | Stronger: prevents all optimization inside the module |

**When to use:** Timing closure on a specific sub-block without propagating logic into/out of it; IP module whose internal structure must not change; verifying a module in isolation before top-level integration.

```systemverilog
(* keep_hierarchy = "yes" *)
module critical_path_block (
    input  logic        clk,
    input  logic [15:0] a, b,
    output logic [31:0] result
);
    // synthesis will not merge this logic with parent module
endmodule
```

### FSM Encoding Control (Vivado)

| Attribute | Value | Effect |
|---|---|---|
| `(* fsm_encoding = "one_hot" *)` | `"one_hot"` | Force one-hot state encoding |
| `(* fsm_encoding = "sequential" *)` | `"sequential"` | Force binary (sequential) encoding |
| `(* fsm_encoding = "gray" *)` | `"gray"` | Force Gray code encoding |
| `(* fsm_encoding = "none" *)` | `"none"` | Let the tool choose; disables automatic re-encoding |

---

## Attribute Syntax Summary

### Vivado (SystemVerilog attribute syntax)

```systemverilog
// On a net/variable
(* dont_touch = "true" *)
logic [7:0] probe_bus;

// On a module instance
(* keep_hierarchy = "yes" *)
my_module u_inst (.clk(clk), .data(data));

// On a module declaration
(* keep_hierarchy = "yes" *)
module my_module (...);
```

### DC / Genus (TCL constraints — applied after `read_design`)

```tcl
# Freeze a specific cell
set_dont_touch [get_cells u_mult/u_pipe_reg]

# Disable boundary optimization on a module
set_boundary_optimization false [get_designs critical_path_block]

# Enable DSP for a module
set_use_dsp true
```

---

## Common Mistakes

| Mistake | Symptom | Correct approach |
|---|---|---|
| Attribute on wrong signal (e.g., on operand instead of output for `use_dsp`) | DSP not inferred | Place attribute on the result register or output wire |
| String value without quotes: `use_dsp = yes` | Syntax error or attribute ignored | Always use quoted strings: `"yes"`, `"block"`, `"true"` |
| Using Vivado attribute in DC flow | Attribute silently ignored | Use `set_dont_touch` / `set_use_dsp` TCL for DC |
| `keep_hierarchy` on a leaf cell | No effect — only meaningful on hierarchical modules | Apply to modules with internal sub-hierarchy |
