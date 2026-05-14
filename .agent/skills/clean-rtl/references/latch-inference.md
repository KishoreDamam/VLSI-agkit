# Latch Inference

> Synthesis infers a latch whenever a signal is *not* assigned in *every*
> branch of a combinational block. Almost every inferred latch is a bug —
> here's how to find them and what to do when one is intentional.

## When a latch is inferred

A latch appears when a combinational block leaves a path through it where
the output is *not* updated. The synthesizer must therefore hold the
previous value — that means storage, that means a latch.

```verilog
// ❌ Latch on z when sel=0
always_comb
    if (sel) z = a;
```

Three classic shapes:

1. **Missing `else`** — most common.
2. **Incomplete `case`** — branches omitted, no `default`.
3. **Conditional assignment under nested control** — assignment in some
   `if` branches but not others.

```verilog
// ❌ z is not assigned when sel=2'b11
case (sel)
    2'b00: z = a;
    2'b01: z = b;
    2'b10: z = c;
endcase
```

## Why latches are usually bad

- **DFT.** Latch-based designs need special scan handling (level-sensitive
  scan, or LSSD). Most projects use flop-only scan, so latches break the
  scan-insertion flow. See `dft-patterns` skill.
- **STA.** Latches enable time borrowing — STA needs the right model
  (`set_max_time_borrow`) or it gives the wrong answer. See `sta` skill.
- **Glitch capture.** A latch is *transparent* when its clock/enable is
  active; glitches on the data side propagate to its output.
- **Lint noise.** Every project lint config flags inferred latches as
  Error severity — accidental latches eat review cycles.

## SystemVerilog: intent-explicit blocks

| Block | Synthesizer enforces | Lint warns if |
|---|---|---|
| `always_comb` | No latch may be inferred | Any signal left unassigned in some path |
| `always_latch` | Latch *must* be the result | Behavior would synthesize as flop or comb |
| `always_ff` | Flop must be the result | Pure-comb logic detected |

Use `always_latch` *only* when you want a latch. `always_comb` is the
default for combinational blocks. Bare `always` is to be avoided in new
code — it disables the synthesizer's intent check.

## Three ways to fix accidental latches

### 1. Complete the conditions

```systemverilog
always_comb
    if (sel) z = a;
    else     z = b;
```

### 2. Default assignment at the top

```systemverilog
always_comb begin
    z = '0;                  // default
    if (sel) z = a;
end
```

Pro: harder to forget when adding new branches.
Con: introduces a "fake" zero output for unspecified states; tests should
catch any test that depends on the default.

### 3. `case` with `default`

```systemverilog
always_comb begin
    case (sel)
        2'b00: z = a;
        2'b01: z = b;
        2'b10: z = c;
        default: z = '0;
    endcase
end
```

`default` is mandatory — it's the only thing that distinguishes "case
covers every value" from "case is missing branches."

## `unique` and `priority` — what they do and don't do

```systemverilog
unique case (sel)
    2'b00: out = a;
    2'b01: out = b;
    2'b10: out = c;
endcase
```

`unique` says: "these cases cover every value and exactly one matches at
any time." If `sel` takes a value not listed (e.g., `2'b11`), the
simulator reports a runtime error; the synthesizer optimizes assuming
the unlisted value never occurs.

`priority` says: "these are the only legal values, evaluated top-down."
Similar runtime check, similar synth optimization.

**Trap:** these keywords *don't* protect against latch inference if some
output is unassigned in some branch.

```systemverilog
// ❌ Latch on out2 — branch 2'b10 doesn't assign it
priority case (sel)
    2'b00: {out1, out2} = {data1, data2};
    2'b01: {out1, out2} = {data3, data4};
    2'b10: out1 = data5;
endcase
```

`priority`/`unique` cover the *case-value* completeness; you still owe
*signal-assignment* completeness on every output, on every branch.

## When a latch is intentional

Genuine latch use cases:

- **Time-borrowing datapaths** (high-frequency designs, classic Intel
  pipelines) — explicit instantiated latch cells.
- **Asynchronous SRAM peripheral wrappers** — latch-based handshakes.
- **Pulse-stretchers** for cross-domain qualifiers (with care — usually a
  flop-based synchronizer is preferred).

For these, **instantiate the library cell** (`LATCH_HI_X1` or similar)
rather than rely on inference. The intent is then unmistakable and
DFT/STA flows can target it correctly.

If you must use `always_latch`:

```systemverilog
always_latch
    if (en) q = d;
```

Document: in the module header *and* in commit message *and* in the
review note, explain why a latch is needed here. Lint will allow but
flag for human review.

## `full_case` and `parallel_case` pragmas — avoid

Legacy Synopsys pragmas:

```verilog
case (sel)  // synopsys full_case parallel_case
    2'b00: z = a;
    2'b01: z = b;
endcase
```

Two problems:

- Pragmas tell the synthesizer "trust me," but the simulator doesn't
  honor them. Sim/synth mismatch if `sel` actually takes 2'b10 or 2'b11.
- Not portable — other tools either ignore or interpret differently.

**Replace with `unique`/`priority`** which *are* portable and *are*
honored by both sim and synth.

## Detection

| Tool | Signal |
|---|---|
| Lint (Spyglass `Latch`, JasperGold `LATCH_INFERRED`) | RTL latches before synth |
| Synthesis report | `INFERRED_LATCH` warnings; `LATCH` cell count > 0 |
| Cell-name grep | `LATCH`, `LAT_X`, `DLAT` patterns in netlist |

Treat every inferred latch in the synthesis report as Error severity.
The right answer is "either the RTL is incomplete, or it should be
`always_latch` with the right cell type."

## Citations

- **Churiwala & Garg**, *Principles of VLSI RTL Design*, §2.5 —
  latch-inference traps and `priority` keyword behavior.
- **IEEE Std 1800-2017 §12.5** — `unique`/`priority` semantics.
- **Cummings**, *"full_case parallel_case — the Evil Twins of Verilog
  Synthesis,"* SNUG Boston 1999 — case-pragma pitfalls.

## See also

- `simulation-race.md` — latch ≠ race; both are surprises but different
  causes.
- `synchronous-reset.md` — reset-inference can produce latches if the
  reset path is ambiguous.
- `dft-patterns` skill — handling intentional latches in DFT.
- `sta` skill `references/latch-timing.md` — time-borrowing model for
  intentional latches.
