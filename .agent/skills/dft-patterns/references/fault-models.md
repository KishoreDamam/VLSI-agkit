# Fault Models — What ATPG Is Testing For

> ATPG generates patterns that exercise specific *fault models*. Each
> model abstracts a class of manufacturing defects. Coverage targets are
> per-model, and modern sign-off requires more than just stuck-at.

## Why fault models exist

A chip has billions of transistors and trillions of possible defects
(shorts between any two metal traces, opens in any via, threshold-voltage
shifts on any device…). Testing for every conceivable defect is
infeasible. Instead, the test community has agreed on *abstract* fault
models: classes of behavior that, if tested for, catch most real defects.

A fault model defines:

1. **Where** the fault could occur (every net, every cell pin, every
   transistor terminal).
2. **What** the fault does (forces the node to a stuck value, slows it,
   shorts it to another).
3. **How** to generate a pattern that detects it (ATPG algorithms).

## Stuck-at fault model

The classic and still the most-tested model.

**Assumption:** any single net (or pin) is either stuck-at-0 (shorted to
ground) or stuck-at-1 (shorted to Vdd). The defect is *binary* and
*static*.

**Pattern requirement:** for stuck-at-0 on node N, generate a pattern
that:
- Drives N to 1 (so the fault makes a difference).
- Propagates N's value to an observable output (so the difference is seen).

Similarly stuck-at-1: drive N to 0 and propagate.

**Coverage target:** 99%+ is standard sign-off. The remaining 1% is
typically untestable: redundant logic, test-mode-only nets, X-blocked
cones.

**Limitations:** stuck-at catches most opens and gross shorts. It
misses:
- Defects that only manifest at speed (transition faults).
- Bridging defects (two nets shorted to each other, not to rails).
- Resistive opens (intermittent, slow).
- Crosstalk-induced delay shifts.

## Transition fault model

Defect that slows a transition but doesn't kill it. Models:
- **Slow-to-rise** — node can go to 1 eventually, but slower than spec.
- **Slow-to-fall** — analogous for high-to-low.

**Pattern requirement:** two-vector pattern. First vector establishes
the starting value; second vector demands a transition. If the
transition doesn't complete before the next clock edge, the fault is
detected.

This is the at-speed test — the second clock edge must be at functional
frequency.

**Coverage target:** 95%+ for modern nodes; some projects target 99%.

**Why it matters:** stuck-at catches the "completely broken" defects;
transition catches the "marginal" defects that pass stuck-at but fail
in the customer's hands. At advanced nodes, marginal defects are the
dominant failure mode.

## Path delay fault model

Like transition, but tests *specific paths* against their measured
delay. A path is good only if its actual silicon delay matches its
characterized delay within a tolerance.

**Pattern requirement:** sensitize a specific path end-to-end; measure
arrival vs expected.

Used for the most timing-critical paths only — full path-delay coverage
is enormously expensive in pattern count.

## Bridging fault model

Two physically adjacent nets shorted to each other (not to rails). The
combined node takes some logical function of both nets — typically AND
(both nets pulled low, behaving like wired-AND) or OR (pulled high).

**Pattern requirement:** drive the two nets to *opposite* values; if
the bridge exists, both nets see the same value, propagating a wrong
result.

**Layout-aware bridging** uses extracted parasitic data to identify
which net pairs *can* physically bridge — pattern count stays bounded.

## IDDQ fault model

Measure quiescent current after each pattern. A defective chip leaks
more than a good one. Detects subtle defects that don't change logic
behavior but increase static power.

**Limited at advanced nodes** — sub-threshold leakage of good devices
swamps defect leakage. Used mainly on older / mixed-signal designs.

## Cell-aware fault models

Patterns target *internal cell defects* — opens inside a flop, shorts
across a specific transistor pair. Foundry-supplied cell-defect lists
specify which internal faults are testable; ATPG synthesizes patterns
for them.

**Cell-aware** is becoming standard for ≤ 28 nm. Adds ~2% coverage
beyond stuck-at + transition for typical libraries.

## Coverage definitions

| Term | Meaning |
|---|---|
| **Test coverage** | Faults detected / total testable faults |
| **Fault coverage** | Faults detected / total faults (including untestable) |
| **ATPG-untestable (AU)** | Tool proved no pattern can detect (redundant logic) |
| **Untestable (UT)** | Untestable for other reasons (test-mode-only, X-blocked) |
| **Not-detected (ND)** | Tool couldn't find a pattern in budget — may be testable, may not |

Sign-off uses test coverage. ND faults need analysis — either prove
untestable (move to AU/UT) or hand-author a pattern.

## What "99% coverage" actually means

A typical sign-off datasheet:

```
Stuck-at:
  Total faults              4,231,567
  Detected                  4,143,876
  ATPG-Untestable              78,234
  Untestable                    9,457
  Test coverage              99.81 %     ← against testable
  Fault coverage             97.95 %     ← against total

Transition:
  Test coverage              96.43 %
  Fault coverage             92.10 %
```

Both numbers matter:
- **Test coverage** says "of what we can test, we tested this much."
- **Fault coverage** says "of all defects, we caught this much."

The gap is the **untestable** count — chip area that no pattern can
exercise. Reducing it requires DFT improvements (more observability,
fewer test-mode-only nets, removing redundancy).

## Mapping faults to actual silicon defects

| Defect (silicon physics) | Best-matching fault model |
|---|---|
| Gate-oxide short | Stuck-at |
| Source/drain open | Stuck-at or transition |
| Metal break (open) | Stuck-at |
| Metal bridge (short) | Bridging or stuck-at |
| Via resistive (slow) | Transition / path delay |
| Sub-threshold leakage | IDDQ (legacy) |
| Random Vth variation | Transition (at corner) |
| Internal cell defect | Cell-aware |

No single model catches everything. Modern sign-off uses **multiple
models in combination**: stuck-at + transition + cell-aware is the
typical ASIC mandate.

## Pattern compression

With multiple fault models, raw pattern counts can hit millions —
exceeding tester memory and runtime. **Compression** (Synopsys
DFTMAX, Cadence Modus EDT, Mentor TestKompress) reduces pattern volume
10× to 100× by:
- Encoding patterns in a compact form.
- Decompressing on-chip into the scan chains.
- Compacting scan-out responses (MISR / XOR networks).

Compression infrastructure costs area (~1–3%) but is mandatory at
modern volumes.

## Common pitfalls

- **Reporting only stuck-at coverage.** At ≤ 28 nm this is incomplete;
  transition is required. Many startups still ship with stuck-at only —
  it bites them in customer returns.
- **Counting AU as coverage.** ATPG-untestable is *not* coverage —
  it's "proven unreachable." Conflating them inflates apparent coverage.
- **Ignoring X-sources.** Uninitialized memory, simulation-only Xs,
  black-box outputs all create X-sources in ATPG. Each propagated X
  blocks observability. The fix is X-masking or scan-load of known
  values — not lower coverage targets.
- **At-speed pattern shifting at functional speed.** Shift uses a slow
  clock; only capture uses functional speed. Forgetting this either
  exceeds tester max-frequency or fails to detect transition faults.

## Citations

- **Bushnell & Agrawal**, *Essentials of Electronic Testing for Digital,
  Memory & Mixed-Signal VLSI Circuits*, Springer 2000 — canonical
  fault-model textbook.
- **Churiwala & Garg**, *Principles of VLSI RTL Design*, §6.1, §6.12 —
  stuck-at intuition and transition-fault rationale.
- **IEEE Std 1450** — Standard Test Interface Language (STIL) for
  patterns.

## See also

- `scan-chains.md` — the infrastructure that lets ATPG patterns reach
  every flop.
- `dft-patterns` SKILL.md — overall DFT methodology.
