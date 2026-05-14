# Simulation Race Conditions

> Race conditions in HDL produce different simulation results depending on
> simulator, version, or compile flags. Same RTL — different behavior. Hunt
> them down before they hide a bug that only shows up in silicon.

## What a race is

A simulation race is RTL that the language allows to be interpreted in more
than one way, all interpretations equally legal. The simulator picks one;
the gates synthesized from the same RTL may behave like a different one.

Races appear almost exclusively in **Verilog**. VHDL has no scheduling
races but has its own delta-delay pitfall (see `feedthrough.md` if added).
SystemVerilog adds constructs that *prevent* races; using them is the cure.

Symptoms:

- Two simulators (or two versions of one simulator) disagree on the same RTL.
- Adding/removing `$display` statements changes simulation results.
- Compile flags (`+rad`, `+race`, `-debug_pp`) shift outputs.
- Gate-level netlist behaves differently from the RTL it was synthesized from.

## Four canonical race patterns

### 1. Combinational Read-Write race

A signal is *assigned* in one `always` block (or `assign`) and *read* in
another `always` whose sensitivity list does not include the assigned signal.

```verilog
// ❌ Race
assign a = b & c;

always @(b or d)
    if (a) o = b ^ d;     // reads `a` but `a` not in sensitivity list
```

When `b` changes, both the `assign` and the `always` trigger. The `if (a)`
result depends on which fires first.

**Fix:** include the read signal in the sensitivity list — or, better,
use SystemVerilog's `always_comb`, which auto-includes every signal read.

```systemverilog
// ✅ Fix
assign a = b & c;
always_comb
    if (a) o = b ^ d;
```

### 2. Sequential Read-Write race

Two `always_ff` blocks on the same clock, one writes a signal the other
reads, using **blocking** assignments.

```verilog
// ❌ Race
always @(posedge clk) b = c;
always @(posedge clk) a = b;
```

If the first fires first, `a` gets the new `b` (i.e., `c`). If the second
fires first, `a` gets the old `b`. Race.

**Fix:** use **non-blocking assignment (NBA)**. With NBA, all RHS are read
first; all LHS update after, so `a` always sees the old `b`.

```systemverilog
// ✅ Fix
always_ff @(posedge clk) b <= c;
always_ff @(posedge clk) a <= b;
```

### 3. Write-Write race

Two concurrent blocks both assign the same signal:

```verilog
always @(b or c)
    if (b != c) err = 1'b1; else err = 1'b0;

always @(b or d)
    if (b == d) err = 1'b1; else err = 1'b0;
```

The last block to fire wins. NBA does not save you here — last-update-wins
applies to NBA too. Synthesis would refuse this (multiple drivers).

**Fix:** never assign the same signal from more than one concurrent block.
Merge into one `always_comb`.

### 4. Initial-Always race

An `initial` block writes a signal that an `always` watches in its
sensitivity list:

```verilog
initial rst_n = 1'b0;
always @(posedge clk or negedge rst_n)
    if (!rst_n) q <= 1'b0; else q <= d;
```

If `always` arms before `initial` runs, it catches the negedge → reset
fires. If `initial` runs first, the negedge happened before `always`
armed → reset missed → flop starts in X.

**Fix (Verilog):** introduce a small explicit delay so the `always` is
guaranteed armed before the edge:

```verilog
initial begin
    rst_n = 1'b1;
    #5 rst_n = 1'b0;
end
```

**Fix (SystemVerilog):** declare with an initializer; that resolves
*before* time 0 and never produces an edge event:

```systemverilog
logic rst_n = 1'b0;
```

## Cummings' 8 NBA guidelines (cite verbatim)

From Cliff Cummings, *"Nonblocking Assignments in Verilog Synthesis,
Coding Styles That Kill!"* SNUG 2000. These prevent essentially every
simulation race in synthesizable RTL:

1. When modeling sequential logic, use non-blocking assignments.
2. When modeling latches, use non-blocking assignments.
3. When modeling combinational logic with an `always` block, use blocking
   assignments.
4. When modeling both sequential and combinational logic within the same
   `always` block, use non-blocking assignments.
5. Do not mix blocking and non-blocking assignments in the same `always`
   block.
6. Do not make assignments to the same variable from more than one
   `always` block.
7. Use `$strobe` (not `$display`) to display values assigned via NBA.
8. Do not make assignments using `#0` delays.

This list is the project-level baseline; lint should enforce all eight.

## SystemVerilog cures (use them)

| Construct | Eliminates |
|---|---|
| `always_comb` | Read-Write races on combinational logic (auto sensitivity) |
| `always_ff` | Mixing seq+comb in one block (lint catches) |
| `always_latch` | Accidental latch → explicit latch declaration |
| Variable initializers (`logic x = 0;`) | Initial-Always race |
| `unique`/`priority` case | Multiple-match write race in case |

If your codebase forbids `always` (bare), `=` in `always_ff`, and `<=` in
`always_comb` — and runs lint with race checks — most races become
unrepresentable.

## Detection

- **Lint:** Spyglass `RACE` family, JasperGold `STRUCT_RACE`, VC SpyGlass
  `STARC-W5.1.x.x`.
- **Simulation race detector:** VCS `-race`, Xcelium `+rad`, ModelSim
  `+RACE`. Run nightly on regression vectors; surface any new hit.
- **Equivalence:** post-synthesis EC (Formal Equivalence Check) will fail
  on RTL that synthesizes one way but simulated another. EC failure on an
  unchanged logic cone is a strong race signal.

## Common pitfalls

- **Adding the read to the sensitivity list "fixes" the race but
  retriggers the block.** Functionally correct, but extra simulation cost.
  Prefer `always_comb` which the simulator can scope efficiently.
- **`#0` delay as a race fix.** Documented as a race generator (rule 8
  above); never reach for `#0` to paper over a race.
- **`always @(posedge clk1 or posedge clk2)`.** Two-clock `always` is
  inherently racy with respect to the second clock; restructure into a
  proper CDC synchronizer.
- **NBA in clock-divider chains.** A divider `clk_div <= ~clk_div;` is
  fine on its own, but feeding the NBA result back as a clock to another
  block causes feedthrough — see Section 2.3.1 of Churiwala & Garg.

## Citations

- **Cliff Cummings**, *"Nonblocking Assignments in Verilog Synthesis,
  Coding Styles That Kill!"* SNUG 2000 — the 8 NBA guidelines above.
- **IEEE Std 1364-2005 §5** — defines the Verilog event-region scheduler;
  races are legal under it.
- **IEEE Std 1800-2017 §9.2.2.2** — `always_comb`, `always_ff`,
  `always_latch` semantics.
- **Churiwala & Garg, *Principles of VLSI RTL Design*, Springer 2011, §2.2** —
  the four race patterns above are presented here in detail.

## See also

- `sim-synth-mismatch.md` — races are one cause of simulation/synthesis
  mismatch but not the only one.
- `latch-inference.md` — incomplete assignments don't cause races but
  cause a related class of surprise.
- `synchronous-reset.md` — reset-related races have their own corner cases.
