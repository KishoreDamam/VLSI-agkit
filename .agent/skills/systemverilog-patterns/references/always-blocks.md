# always Blocks Reference — SystemVerilog

## The four forms compared

| Form | Sensitivity list | Latch check | Tool-checked comb? | Use in RTL? |
|---|---|---|---|---|
| `always_ff @(posedge clk ...)` | Explicit; errors if wrong | No (is sequential) | No | Yes — clocked logic |
| `always_comb` | Automatic (all reads) | Yes — no undriven outputs | Yes | Yes — combinational |
| `always_latch` | Automatic | Yes — latches intended | Latch | Rarely; prefer registers |
| `always @*` | Automatic (reads only) | No | No | Legacy only |
| `always @(...)` | Manual | No | No | Never in new code |

---

## always_ff — clocked sequential logic

`always_ff` enforces:
1. The sensitivity list must contain only edge events.
2. The compiler errors if the list does not include all clock/reset edges that
   drive the block.

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        q <= '0;
    else
        q <= d;
end
```

Rules:
- Use **non-blocking assignment** (`<=`) inside `always_ff`. Blocking assignment
  (`=`) in a clocked block causes simulation-vs-synthesis mismatch.
  (IEEE 1800-2017 §10.4.2)
- Do not mix blocking and non-blocking in the same `always_ff` block.
- Never read a signal that you also write in the same `always_ff` unless it is
  a deliberate self-loop (e.g., a counter).

---

## always_comb — combinational logic

`always_comb` enforces:
1. Automatic sensitivity: all signals **read** in the block are in the sensitivity
   list, including signals read inside functions called from the block.
2. If any output is not assigned on all paths, the tool reports a latch.

```systemverilog
always_comb begin
    result = '0;       // default assignment prevents latch
    case (sel)
        2'b00: result = a;
        2'b01: result = b;
        2'b10: result = c;
        // 2'b11 falls through to default '0
    endcase
end
```

Best practice: assign defaults before the `case`/`if` so every path drives every
output. This is both correct and documents intent.

---

## always_latch — intentional latches

Use only when a latch is architecturally required (rare in synchronous ASIC design).
`always_latch` is the same as `always_comb` for sensitivity purposes, but the tool
suppresses the "unintended latch" warning.

```systemverilog
always_latch begin
    if (latch_en)
        latched_data = data_in;   // transparent when en=1
    // when latch_en=0, latched_data holds
end
```

---

## always @* — legacy automatic sensitivity

Behavior is identical to `always_comb` in simulation for the sensitivity list, but:
- No latch inference check.
- Does not include signals read inside function calls in the sensitivity list
  (tool-dependent; some tools do include them).
- No compile-time error for missing sensitivity signals.

Verdict: `always @*` is a Verilog-2001 idiom. Use `always_comb` in new SV code.

---

## always @(...) — manual sensitivity list

Manual sensitivity lists are fragile. Missing a signal causes simulation/synthesis
mismatch (synthesis treats all reads as sensitive; simulation misses the omitted signal).

```systemverilog
// BAD — b is not in sensitivity list
always @(a) begin
    result = a & b;   // simulation: stale when b changes; synthesis: correct
end

// CORRECT equivalent
always_comb begin
    result = a & b;
end
```

The only valid use of `always @(...)` is legacy testbench code with explicit event
triggers, e.g., `always @(posedge clk)` — but even that should be `always_ff` in RTL.

---

## Latch inference — how it happens and how to prevent it

A latch is inferred when an output of an `always_comb` (or `always @*`) block is not
driven on every code path:

```systemverilog
// LATCH INFERRED — y not driven when sel==0
always_comb begin
    if (sel)
        y = a;
    // else: y is not assigned -> latch
end

// CORRECT — default assignment
always_comb begin
    y = '0;           // default
    if (sel)
        y = a;
end
```

Common sources of accidental latches:
- `if` without `else` in an `always_comb` block.
- `case` that does not cover all encodings without a `default`.
- A sub-signal of a struct assigned only in some branches.

---

## Simulation/synthesis mismatch risk

The most dangerous mismatch: a signal that drives combinational logic is missing
from a manual sensitivity list.

- **Simulation** evaluates the block only when listed signals change.
- **Synthesis** implements the combinational function based on all reads.
- Result: simulation shows correct behavior, but the real hardware is different.

`always_comb` eliminates this class of bug. `always @(...)` does not.

---

## Citations

- IEEE 1800-2017 §9.2.2.2: `always_comb` — automatic sensitivity and latch check.
- IEEE 1800-2017 §9.2.2.3: `always_latch` — intentional latch.
- IEEE 1800-2017 §9.2.2.4: `always_ff` — sequential sensitivity enforcement.
- IEEE 1800-2017 §10.4.2: Non-blocking vs blocking assignment semantics.
