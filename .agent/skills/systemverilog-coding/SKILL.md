---
name: systemverilog-coding
description: Use when writing SystemVerilog RTL and unsure about `logic` vs `reg` vs `wire`, `always_comb` vs `always @*` vs `always @(...)`, interface/modport syntax, multiple drivers on struct fields, or pipelined modules with generate-for.
---

# SystemVerilog Patterns

> Canonical SV2017 coding patterns for RTL design: data types, interfaces, procedural blocks, and generate constructs.

## When to use

- You are writing new RTL and need the correct SV type (`logic` vs `reg` vs `wire`).
- You need a parameterized interface with valid/ready handshake and modports.
- You are getting "multiple drivers" errors on struct fields from two `always` blocks.
- You need to know when `always_comb` vs `always @*` vs `always @(...)` causes simulation/synthesis mismatch.
- You are building a pipelined module where the number of stages is a parameter.
- You are migrating Verilog-2001 code to SystemVerilog.

## Quick reference

| Pattern | Use when | Anti-pattern |
|---|---|---|
| `logic` everywhere | All new RTL signals | `reg` / `wire` in new SV code |
| `always_ff` + `<=` | Clocked sequential | `always @(posedge clk)` + `=` |
| `always_comb` + default assign | Combinational logic | `always @(...)` manual sensitivity |
| `always_latch` | Intentional latch only | Accidental latch from missing `else` |
| Interface + modports | Multi-signal bus | Flat port lists for reused buses |
| One `always_ff` per struct | Whole struct per block | One field per block → multiple drivers |
| `generate-for` + `genvar` | N identical hardware copies | Copy-pasted blocks for each N |
| `initial assert (P >= 1)` | Parameter validation | Silent wrong-parameter elaboration |

## Core patterns

### 1. logic vs reg vs wire — the one rule

**Use when:** declaring any RTL signal, input/output port, or combinational wire.

```systemverilog
// NEW SV: use logic for everything
logic        clk, rst_n, valid;
logic [31:0] data;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) data <= '0;
    else        data <= data_in;
end

assign count_next = count + 1;  // continuous assign: logic is fine
```

- **Gotchas:**
  - `reg` does not imply a flip-flop in Verilog-2001; `logic` is cleaner and compiler-enforced.
  - Use `wire` only for tri-state nets or legacy module port connections.
  - `logic` rejects multiple `always_*` drivers at compile time — use this feature.

> Full type reference (packed/unpacked arrays, structs, unions, typedef): `references/data-types.md`.

---

### 2. Parameterized interface with valid/ready modports

**Use when:** connecting a producer and consumer with a multi-signal handshake bus.

```systemverilog
interface valid_ready_if #(parameter int DATA_WIDTH = 32) (
    input logic clk, rst_n
);
    logic                  valid, ready;
    logic [DATA_WIDTH-1:0] data;

    modport producer (input clk, rst_n, output valid, data, input ready);
    modport consumer (input clk, rst_n, input valid, data, output ready);
endinterface

// Instantiation at top level or testbench:
valid_ready_if #(.DATA_WIDTH(64)) u_bus (.clk(clk), .rst_n(rst_n));
my_producer u_prod (.bus(u_bus.producer));
my_consumer u_cons (.bus(u_bus.consumer));
```

- **Gotchas:**
  - iverilog 12 does not support `interface_type.modport_name` in module port declarations. Use full vendor simulators (VCS, Questa, Xsim) or omit the modport specifier in the port for iverilog.
  - Clock and reset are passed as inputs to the interface — they are not generated inside it.
  - Modports enforce direction at instantiation; a wrong-direction assignment is a compile error.

> See `examples/valid_ready_if.sv` for the full producer/consumer implementation.
> Deep reference: `references/interfaces-and-modports.md`.

---

### 3. Multiple drivers on struct fields — the correct patterns

**Use when:** two `always_ff` blocks each drive a different field of the same packed struct.

```systemverilog
// WRONG: two blocks each driving one field of the same struct
// -> "multiple drivers" error
typedef struct packed { logic [15:0] addr; logic [15:0] data; } pkt_t;
pkt_t pkt;                                  // two drivers below — this is the bug
always_ff @(posedge clk) pkt.addr <= a;    // driver 1
always_ff @(posedge clk) pkt.data <= d;    // driver 2 — ERROR

// CORRECT pattern A: one always_ff drives the whole struct
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin pkt.addr <= '0; pkt.data <= '0; end
    else        begin pkt.addr <= a;  pkt.data <= d;  end
end

// CORRECT pattern B: split into separate logic variables
logic [15:0] pkt_addr, pkt_data;
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) pkt_addr <= '0;
    else        pkt_addr <= a;
end
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) pkt_data <= '0;
    else        pkt_data <= d;
end
assign pkt = {pkt_addr, pkt_data};   // combine at the wire level
```

- **Gotchas:**
  - SystemVerilog requires single-driver semantics per `logic` variable — even individual fields of a packed struct are part of the same signal.
  - Pattern B is preferred when the two fields are driven by logically independent state machines.

---

### 4. always_comb vs always @\* vs always @(...)

**Use when:** choosing which procedural block to use for combinational logic.

```systemverilog
// BEST: always_comb — tool-checked, full auto-sensitivity
always_comb begin
    y = '0;           // default prevents latch
    if (sel) y = a;
end

// LEGACY OK: always @* — auto-sensitivity, no latch check
always @(*) begin
    y = '0;
    if (sel) y = a;
end

// DANGEROUS: manual sensitivity — simulation/synthesis mismatch risk
always @(sel) begin   // BUG: b not listed
    y = a & b;        // synthesis: correct; simulation: stale when b changes
end
```

- **Gotchas:**
  - `always @(...)` missing a signal causes synthesis to be correct but simulation to be wrong — the hardest class of mismatch to debug.
  - `always_comb` reports a latch if any output is undriven on some path; `always @*` does not.
  - `always_comb` includes signals read inside function calls in the sensitivity list; `always @*` behavior for functions is tool-dependent.

> Detailed comparison with latch-inference rules: `references/always-blocks.md`.

---

### 5. Pipelined module with N stages using generate-for

**Use when:** building an N-stage data pipeline where N is a compile-time parameter.

```systemverilog
module pipeline #(parameter int STAGES = 4, parameter int WIDTH = 32) (
    input  logic             clk, rst_n,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);
    initial assert (STAGES >= 1)
        else $fatal(1, "pipeline: STAGES must be >= 1");

    logic [WIDTH-1:0] stage [0:STAGES-1];
    assign data_out = stage[STAGES-1];

    genvar i;
    generate
        for (i = 0; i < STAGES; i++) begin : gen_pipe
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n)  stage[i] <= '0;
                else if (i == 0) stage[i] <= data_in;
                else             stage[i] <= stage[i-1];
            end
        end
    endgenerate
endmodule
```

- **Gotchas:**
  - `assign stage[0] = data_in` is rejected by iverilog when `stage` is a `logic` array. Use the `else if (i == 0)` branch inside `always_ff` instead. The `stage[-1]` reference in the dead `else` branch is never elaborated for `i=0` because `i` is a genvar (elaboration constant). Vendor tools (VCS, Questa) also accept `assign stage[0]` directly.
  - Label generate blocks (`gen_pipe`) for hierarchical references and waveform viewers.
  - Parameter validation with `$fatal` runs at elaboration and gives a clear error.

> Edge cases, nested generate, and hierarchical references: `references/generate-constructs.md`.
> Self-checking testbench: `examples/tb_pipeline.sv`.

---

## Anti-patterns (do NOT do this)

1. **`reg` or `wire` in new SystemVerilog** — `logic` is the universal replacement; `reg`/`wire` add confusion without benefit in SV.
2. **Blocking assignment (`=`) in `always_ff`** — causes simulation/synthesis mismatch; NBA (`<=`) is required in clocked blocks. (IEEE 1800-2017 §10.4.2)
3. **`always @(...)` with manual sensitivity lists in RTL** — one missing signal is a latent simulation bug that synthesis silently "fixes," masking the error.
4. **Driving struct fields from multiple `always` blocks** — each `logic` variable has exactly one driver rule; sub-field assignment does not bypass this.
5. **No default assignment in `always_comb`** — any undriven output path infers a latch; assign defaults at the top of the block.
6. **Interfaces with hardcoded widths** — parameterize `DATA_WIDTH` from day one; retrofitting requires changing the interface and all connected modules.

---

## Validation checklist (before declaring code "done")

- [ ] All RTL signals use `logic`; no `reg` or `wire` except for wired nets or legacy ports.
- [ ] All clocked blocks use `always_ff` with non-blocking assignment (`<=`).
- [ ] All combinational blocks use `always_comb` with a default assignment before the `case`/`if`.
- [ ] No manual sensitivity lists in RTL (`always @(a, b, ...)` → `always_comb`).
- [ ] Each `logic` signal is driven by exactly one `always_ff` or one `always_comb` or one `assign`.
- [ ] Parameterized modules have `initial assert` parameter checks with `$fatal`.
- [ ] Generate blocks have unique labels for hierarchical reference.
- [ ] Interface ports include clock and reset as inputs; modports list them under `input`.
- [ ] Packed structs used in hardware are `typedef struct packed`; unpacked structs are TB-only.

---

## Citations

- IEEE 1800-2017 §6.11.2 — `logic` type: 4-state variable, single-driver enforcement.
- IEEE 1800-2017 §9.2.2.2 — `always_comb`: automatic sensitivity, latch inference check.
- IEEE 1800-2017 §9.2.2.4 — `always_ff`: sequential sensitivity enforcement.
- IEEE 1800-2017 §10.4.2 — Non-blocking assignment semantics in clocked blocks.
- IEEE 1800-2017 §7.4.1 — Packed struct bit layout: first-declared field = MSB.
- IEEE 1800-2017 §25 — Interface definitions, modports, clocking blocks.

---

## See also

- `references/data-types.md` — logic/reg/wire migration, packed/unpacked arrays, structs, unions, typedef
- `references/interfaces-and-modports.md` — parameterized interfaces, modports, clocking blocks, synthesis gotchas
- `references/always-blocks.md` — always_ff/always_comb/always_latch vs always @\*; latch inference; simulation/synthesis mismatch
- `references/generate-constructs.md` — generate-for/if, parameter validation, pipelined arrays, hierarchical references
- `examples/valid_ready_if.sv` — parameterized valid/ready interface with producer + consumer modports (requires VCS/Questa/Xsim; iverilog limitation noted)
- `examples/pipeline.sv` — N-stage pipeline using generate-for
- `examples/tb_pipeline.sv` — self-checking testbench for pipeline.sv; runs with iverilog -g2012
