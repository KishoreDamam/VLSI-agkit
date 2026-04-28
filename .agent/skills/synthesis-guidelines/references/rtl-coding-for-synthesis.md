# RTL Coding for Synthesis

> Patterns and anti-patterns for writing SystemVerilog that synthesizes correctly — no latches, no combinational loops, no X-propagation surprises.

---

## Latch Inference

A latch is inferred whenever a combinational `always_comb` block (or `always @(*)`) does not assign a signal in every possible code path. The synthesizer must preserve the previous value, which requires a level-sensitive latch cell.

### Why incomplete `if`/`case` causes a latch

```systemverilog
// BAD: latch on 'out' — missing else branch
always_comb begin
    if (sel)
        out = a;
    // 'out' is unassigned when sel==0 — synthesizer infers a latch
end
```

The fix is a **default assignment before the conditional**:

```systemverilog
// GOOD: default eliminates the latch
always_comb begin
    out = '0;       // covers all unspecified branches
    if (sel)
        out = a;
end
```

### `unique case` adds enforcement, not a substitute for default

`unique case` tells the tool that at most one branch fires and all legal encodings are covered. It eliminates the latch on the *case expression* signal, but does **not** help any output signals that are missing assignments in some branches. Always add a default output assignment before the `case` regardless.

```systemverilog
always_comb begin
    decoded = '0;               // output default — prevents latch
    unique case (opcode)        // unique: no priority encoding needed
        OP_ADD: decoded = ADD_CTRL;
        OP_MUL: decoded = MUL_CTRL;
        OP_NOP: decoded = NOP_CTRL;
        // all legal opcodes covered — unique case validates this
    endcase
end
```

### Synthesis lint keywords to watch

- Vivado: `WARNING: [Synth 8-327] Latch inferred for variable <signal>`
- DC: `Warning: Latch inferred for variable <signal>`
- Xcelium lint: `%W,LATCHNO`

---

## Combinational Loop Detection

A combinational loop exists when a combinational output feeds back to its own input without any register in the path. Synthesis tools warn because:

1. The loop has no stable DC operating point.
2. Simulation and silicon behavior diverge.
3. Timing analysis cannot close on a path with no register.

### Common pattern: async feedback

```systemverilog
// BAD: combinational loop — out feeds back into logic computing out
assign out = (sel ? in : out) & enable;
```

### Breaking the loop with a register

```systemverilog
// GOOD: register breaks the loop
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) out <= '0;
    else        out <= (sel ? in : out) & enable;
end
```

### Synthesis lint keywords to watch

- Vivado: `WARNING: [Synth 8-295] Sequential element <name> is unused`; `CRITICAL WARNING: [Synth 8-6849] Combinational loop`
- DC: `Warning: Combinational loop found`

---

## Reset Coding

### Canonical form: asynchronous active-low reset

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        q     <= '0;
        state <= IDLE;
    end else begin
        q     <= d;
        state <= next_state;
    end
end
```

**Why asynchronous reset assertion:** The register clears immediately when `rst_n` falls — no clock edge required. This guarantees a known state before the first clock edge.

**Why synchronous deassertion (async reset, sync deassert pattern):**

```systemverilog
// Reset synchronizer — deassert rst_n only on clock edge to prevent metastability
logic rst_n_sync1, rst_n_sync2;
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) { rst_n_sync2, rst_n_sync1 } <= 2'b00;
    else        { rst_n_sync2, rst_n_sync1 } <= { rst_n_sync1, 1'b1 };
end
// Use rst_n_sync2 as the reset to downstream logic
```

### Why `initial` is simulation-only

`initial` blocks execute once at time zero in simulation. Synthesis tools (Vivado, DC, Genus) **silently discard all `initial` statements** — they have no hardware equivalent in FPGA fabric or standard-cell libraries. Any signal whose only initialization is an `initial` block will start as X in gate-level simulation.

**Rule:** Every register that needs a known power-up value must be initialized by the reset path in `always_ff`.

---

## Interface Synthesis

### What is synthesizable

| Construct | Synthesizable? | Notes |
|---|---|---|
| `interface` with `modport` | Yes | Fully synthesizable in Vivado and DC |
| `interface` port parameters | Yes | Parameterized interfaces synthesize correctly |
| `interface` arrays | Yes (Vivado 2020+) | Check DC version for support |
| `virtual interface` | No | Simulation-only; OOP handle; not hardware |
| `interface` in a `class` | No | Class context is UVM/simulation only |
| Clocking block in interface | Partial | Synthesizes in some tools; check vendor docs |

### Using `modport` for synthesis boundaries

```systemverilog
interface axi_if #(parameter DW = 32) (input logic clk, rst_n);
    logic [DW-1:0] wdata;
    logic          wvalid, wready;

    modport master (output wdata, wvalid, input wready, input clk, rst_n);
    modport slave  (input  wdata, wvalid, output wready, input clk, rst_n);
endinterface

module my_master (axi_if.master axi);
    // synthesizable — axi.wdata, axi.wvalid, axi.wready are plain logic
endmodule
```

---

## X-Propagation Hazards

### How RTL sim masks X

In RTL simulation, many operators produce a "defined" result even with X inputs. For example:

```
X & 0 = 0   (RTL sim: 0 wins)
X | 1 = 1   (RTL sim: 1 wins)
```

Synthesis assumes X is a don't-care and may optimize the logic in a way that exposes X paths that RTL sim hid.

### Gate-level sim propagates X pessimistically

In GLS, every gate computes X if any input is X (except for the masking cases above). This means:

- A reset that doesn't reach every register leaves some registers at X.
- X then propagates forward through combinational logic, potentially corrupting outputs.
- The simulation may fail (or give false passes if X is incorrectly masked).

### `casex`/`casez` create X-masking hazards

```systemverilog
// BAD: casex treats X and Z as don't-care in the case expression
// Synthesis sees a different truth table than RTL sim under X inputs
casex (sel)
    2'b1x: out = a;   // matches 10 and 11 — AND matches when sel has X bits
endcase

// GOOD: use unique case or case with fully specified values
unique case (sel)
    2'b10: out = a;
    2'b11: out = b;
    default: out = '0;
endcase
```

**Rule:** Avoid `casex`/`casez` in synthesized RTL. Use `case` with explicit don't-care coverage via `default`.

### Full reset coverage requirement

Every register in the design must be reachable by the reset sequence. Use:
- `report_clock_interaction` (Vivado) to find registers not connected to a reset net.
- Formal tools (`check_reset` in Jasper/VC Formal) for exhaustive coverage.
- GLS with reset sequence as the first test vector to expose any X-propagation.
