# Simulation–Synthesis Mismatch

> RTL simulation passes; the synthesized gate-level netlist, run with the
> same vectors, fails. The list of causes is short and well-known — recognize
> them at code review time.

## What it is

You write RTL, simulate it, it produces output X. You synthesize the same
RTL, simulate the netlist with the same vectors, it produces output Y ≠ X.
Either the RTL was ambiguous (and the simulator and synthesizer interpreted
it differently), or you used constructs synthesis silently dropped.

This is a major source of silicon bugs. Formal Equivalence Check (EC)
catches most cases but only if the language constructs are within EC's
scope; some mismatch sources are *outside* EC entirely (e.g., initial
blocks).

## The eight canonical causes

### 1. Simulation races

See `simulation-race.md`. The simulator picks one interpretation, the
synthesized circuit may behave like a different one.

### 2. Explicit timing in synthesizable RTL

```verilog
always @(posedge clk)
    q <= #1 d;          // ❌ delay ignored by synthesis
```

Synthesis treats `#1` as zero. If the design relies on the delay (e.g.,
to align with another delayed path), the gate-level behavior diverges.

**Fix:** never put explicit `#` delays in synthesizable code. Restrict
them to testbench drivers and clock generators.

### 3. Missing sensitivity list signals

```verilog
always @(a or b)        // sel missing!
    if (sel) z = a; else z = b;
```

RTL sim: `z` does *not* update on `sel` changes (block isn't triggered).
Synthesis builds a 2:1 mux that *does* respond to `sel`. Gate-level sim
differs from RTL sim.

**Fix:** `always_comb` — auto-builds the sensitivity list.

### 4. Initial blocks

```verilog
reg [7:0] q;
initial q = 8'hAA;       // ❌ ignored by synthesis
```

Simulation: `q` starts at `0xAA`. Synthesis: dropped → flop starts X
(ASIC) or in the power-on value of the SRAM/flop primitive (FPGA).

**Fix:** initial blocks belong in testbenches, not designs. For real
power-on values, use a synchronous or asynchronous reset cycle.

(FPGA exception: Xilinx/Intel synthesizers honor `initial` for register
power-on values, but that hides the issue if you ever port to ASIC. Treat
`initial` as testbench-only by policy.)

### 5. Dependency on X

```verilog
if (sel === 1'bx) q = error;   // ❌
```

`x` exists only in simulation. Silicon has 0 or 1. RTL sim sees the `x`
and takes the branch; gates take the *0* or *1* branch on whatever the
silicon happens to settle to. Behaviors diverge.

**Fix:** never make functional decisions based on `===`, `!==`, `casex`,
`casez`, or comparisons to `x`/`z`. Reserve them for testbench checking
only. The `safe_casez` patterns are an exception with strict review.

### 6. Comparison with `z` (tri-state)

Same shape as the X case. `z` means "high-impedance" in simulation, but
on-chip the bus has *some* DC value pulled up or pulled down. Comparing
to `z` is meaningless in silicon and yields a different result than RTL
simulation predicted.

### 7. Delta-delay (VHDL) and feedthroughs

VHDL signal assignment introduces a "delta cycle" — infinitesimal delay.
RTL relying on a specific delta count gets a different post-synthesis
ordering once buffers/optimizations change the delta chain. See
`feedthrough.md` (if present) for the full pattern.

**Fix:** never rely on delta-balancing for correctness. Use explicit
clocking; insert pipeline registers where ordering matters.

### 8. Careless use of variables (VHDL)

```vhdl
process(rst_n, clk)
    variable v : std_logic;
begin
    v := '0';                          -- sim sees, synth keeps for inferred wire
    if rising_edge(clk) then
        q <= data;
        v := '1';                      -- ❌ second assignment - synth ignores
    end if;
    sig1 <= v;                         -- mismatch hides here
end process;
```

The variable's value crosses the clocked branch. Synthesis ignores the
second assignment; simulation honors it. `sig1` diverges.

**Fix:** avoid VHDL `variable` declarations in synthesizable RTL (per
the Mentor/Synopsys Reusability Methodology Manual). Use `signal`.

## Catch-all detection

| Tool / check | What it finds |
|---|---|
| Lint (Spyglass `LINT`, JasperGold `STRUCT`) | Missing sensitivity, `#` in always_ff, dependency on `x`/`z` |
| Formal Equivalence (Conformal, Formality) | Most logic mismatches, not initial-block divergence |
| Gate-level simulation (GLS) with SDF | Exposes timing-dependent mismatch (delta, race) |
| Coverage-driven sims with X-pessimism | Forces `x` propagation; flushes out X-dependent branches |

## Project policy that eliminates 90%

1. `always_comb` / `always_ff` / `always_latch` only — never bare `always`.
2. ` `default_nettype none ` at file top.
3. No `#` delays outside testbench files.
4. No `initial` blocks outside testbench files.
5. No `===`, `!==`, `casex`, `casez` in functional decisions.
6. Lint must run clean before commit; race detector runs nightly.
7. Formal Equivalence on every netlist drop, against the RTL it came from.

## Citations

- **Cliff Cummings**, *"Synthesizable RTL Coding Practices to Avoid
  Simulation-to-Synthesis Mismatches,"* SNUG 1999.
- **Mentor/Synopsys**, *Reusability Methodology Manual* — recommends
  against VHDL `variable` for cross-process state.
- **Churiwala & Garg**, *Principles of VLSI RTL Design*, §2.4.
- **IEEE Std 1364-2005 §5** — Verilog scheduling; explains `#` and
  sensitivity list semantics.

## See also

- `simulation-race.md` — the largest single class of mismatch.
- `latch-inference.md` — accidentally inferred latches are themselves a
  mismatch source (sim and synth agree on the latch, the *designer*
  didn't intend it).
- `synchronous-reset.md` — sync reset inference differs across synth tools.
