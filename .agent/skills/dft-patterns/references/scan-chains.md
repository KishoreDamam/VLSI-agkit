# Scan Chains — Controllability and Observability

> Scan replaces ordinary flops with scan-flops, chains them, and gives every
> sequential element direct controllability *and* observability — without
> adding hundreds of primary I/O pins.

## The controllability/observability problem

Stuck-at fault testing on a single AND gate is easy: drive both inputs
to known values, observe the output. In a real chip the gate sits deep
inside the cone of logic — getting a value *to* its inputs requires
controlling many other gates upstream, and *observing* its output
requires propagating the value through many gates downstream.

**Controllability gets harder near the output.** A gate near the chip's
primary outputs is easy to observe (it's right there) but hard to
control (you have to drive a sequence through the entire pipeline to
reach it).

**Observability gets harder near the input.** A gate near the chip's
primary inputs is easy to control (drive its inputs directly) but hard
to observe (you have to propagate its output through the whole pipeline
to a primary output).

Adding more I/O pins solves the problem in theory — give every internal
node a tap. In practice you'd need thousands of extra pins; package and
die-size cost is prohibitive.

## Scan as the solution

Replace every ordinary flop with a **scan flop** — a flop with a
test-mux on its D input:

```
              ┌─ regular path ──┐
   D ─────────┤                  ├──→ FF ──→ Q
              │     0           │
   SI ────────┤  TE-mux          │
              │     1           │
              └─── scan path ────┘
                      ▲
                      │
                     SE (scan enable)
```

When `SE = 0`, the flop captures its functional `D`. When `SE = 1`, it
captures `SI` (scan-in), which is the previous flop's `Q`. With all
flops chained, you can shift any pattern of values into the chain on
successive clock edges — and shift out captured values likewise.

```
SI → FF1 → FF2 → FF3 → … → FFN → SO
```

The chain turns every flop into both a primary input (controllability:
shift in any value) and a primary output (observability: shift the value
to SO).

## Capture vs Shift modes

| Mode | `SE` | What happens |
|---|---|---|
| **Shift** | 1 | All flops act as a chain — shift one bit per clock |
| **Capture** | 0 | All flops sample their functional `D` for one cycle |

A typical ATPG test pattern is *shift–capture–shift*: shift in a stimulus
pattern, run one (or a few) functional clocks to capture the response,
then shift out and compare.

## At-speed test

Stuck-at faults are detected by single-cycle capture. **Transition faults**
(slow-to-rise / slow-to-fall) require *two* functional clocks at the
operating frequency — a "launch" and a "capture" — so the silicon must
actually toggle at the target rate. This is "at-speed test."

At-speed test puts heavy demands on test mode:

- Capture clock at functional frequency, not slow shift clock.
- Tester must deliver fast launch-to-capture edges.
- Power network must support the switching activity of the entire chain
  at functional speed (often more than functional power consumption).

## Number of scan chains — balancing

A single chain through millions of flops is slow (one shift per cycle).
Modern designs use **N parallel scan chains** (typically 8–64+) so total
test time scales as (max chain length / chip frequency).

```tcl
# DFT Compiler example
set_scan_configuration -chain_count 16
set_scan_configuration -clock_mixing mix_clocks   ;# allow mixing across clock domains
```

Balancing rule: every chain should be within ~10% of the longest. ATPG
runtime is bounded by the longest chain.

Crossing clock domains in a chain requires a **lock-up latch** between
the two flops — a half-cycle latch that prevents hold-time races during
shift. Tools insert these automatically.

## Crossing power domains

Scan-shift through a powered-down domain corrupts the chain (the
powered-down flops can't shift). Two options:

- **Isolate the powered-down domain from the chain** (skip its flops
  during shift).
- **Power up all domains during scan-test mode** (test pattern starts
  with power-up sequence).

Both have downsides — pick per project policy and document in the test
protocol file.

## Non-scannable elements (the DFT-fixers list)

| Structure | Why scan breaks | Fix |
|---|---|---|
| **Transparent latches** | Level-sensitive — shift races through them | Replace with flop, or use LSSD scan, or isolate behind a test-mux |
| **Async reset** | During shift, an asserted reset would clear all flops | Mux the reset with `test_en` so it deasserts in test mode |
| **Gated clock** | During shift, the gate may block the scan clock | Library ICG with `TE` (test enable) input that bypasses the gate condition |
| **Combinational feedback loop** | ATPG can't sensitize a stable pattern | Break the loop with a test-only mux (`scan_loop_break`) |
| **Internally-generated clocks** (clock dividers, ring oscillators) | Shift needs a single common scan clock | Bypass-mux the divider; drive scan clock direct from tester pin |
| **Memories** | Scan can't reach inside SRAM | MBIST (separate controller, see `dft-patterns` SKILL.md) |
| **Black-box IP** | Internal flops not visible | Boundary scan around the IP, MBIST if memory, or trust the IP vendor's pattern set |

## Scan I/O pins

Minimum scan I/O on a chip:

- `scan_in[N-1:0]` — one per chain.
- `scan_out[N-1:0]` — one per chain.
- `scan_enable` — global, controls shift/capture.
- `test_mode` (or `dft_mode`) — global, qualifies async-reset bypass, ICG
  bypass, etc.

These are often **pin-muxed** with functional pins (a functional-mode
pin that becomes scan-in when `test_mode=1`). See
`timing-constraints` skill `references/false-paths-catalog.md` Category 5
for the SDC implications.

## What scan tells the ATPG tool

ATPG generates test patterns assuming every flop is directly
controllable and observable via the chain. The synthesizer + DFT
insertion produces:

- The scan chain order (`scan_chain_order.spf`).
- The test protocol — clock waveforms, reset sequencing, shift count.
- The pattern file (`*.stil`, `*.wgl`, `*.vcd`) for the tester.

If any of those is wrong (chain mis-ordered, clock not running, reset
not bypassed), the patterns fail — not because of silicon, but because
the tester saw what the ATPG didn't expect.

## DFT DRC — fix-before-scan

`dft_drc` checks:

- `clock_drc` — every flop's clock can be controlled by a scan clock.
- `reset_drc` — every async reset can be bypassed in scan.
- `data_drc` — no uncontrollable feedback / bus conflicts.
- `coverage_estimate` — fraction of flops that can be reached.

Run `dft_drc` *before* `insert_dft`. Every violation must be fixed at
RTL or with explicit DFT directives — `insert_dft` cannot fix what DRC
flagged. See `synthesis-guidelines` for upstream RTL practices.

## Common pitfalls

- **Latches "hidden" in always_comb.** Lint clean ≠ scan clean. The
  synthesizer might infer latches that DFT then chokes on.
- **`test_en` not in the sensitivity list.** RTL with `if (test_en)` in
  the comb logic but `test_en` not declared as a top-level mode signal
  → DFT can't recognize it as the test mode.
- **Forgotten scan chain on reused IP.** Importing a vendor block
  without its scan chain leaves a hole in coverage. Either rebuild the
  chain through the IP or wrap it (IEEE 1500 SECT).
- **At-speed not verified in simulation.** RTL functional sim doesn't
  exercise the launch-capture path. Run gate-level sim with SDF
  back-annotation on the ATPG patterns before tape-out.
- **MBIST and LBIST collisions.** Both want the scan clock; arbitration
  needs explicit pri/sec mode bits.

## Citations

- **Churiwala & Garg**, *Principles of VLSI RTL Design*, §6.3–6.5 —
  controllability/observability, scan-flop mechanics, shift/capture.
- **IEEE Std 1500-2005** — embedded core test wrapper (SECT) for IP.
- **IEEE Std 1149.1** — JTAG boundary scan.

## See also

- `fault-models.md` — what scan is testing *for* (stuck-at, transition).
- `dft-patterns` SKILL.md — DFT overview and BIST.
- `synthesis-guidelines` skill — DFT-aware RTL coding.
- `timing-constraints` skill `references/false-paths-catalog.md` —
  multi-mode SDC for functional vs scan.
