# Congestion-Aware RTL

> Routing congestion is a back-end problem, but its root cause is often in
> RTL. RTL patterns that *will* congest are recognizable before you ever
> see a placement.

## What congestion is

After synthesis and placement, the design has to be routed — every cell
pin connected through metal layers. Wires run only along **tracks** in
fixed directions (horizontal on one layer, vertical on the next, with
vias to change layer). Wires cannot diagonally cross — they zigzag along
tracks.

**Congestion** is when too many wires need to occupy a small physical
area. Symptoms:

- **Local congestion** — a hot spot in one block. Mild: routing detours
  add delay and capacitance. Severe: cannot route, design fails physical
  closure.
- **Global congestion** — whole-chip routing demand exceeds supply. Need
  to grow die size, refactor blocks, or fundamentally rework an RTL hot
  spot.

The fix is much cheaper at RTL than at place-and-route.

## RTL patterns that create congestion

### 1. High utilization

Utilization = (area of all cells in a block) / (area of the block). High
utilization means cells are packed tight, leaving few tracks open for
wires. Typical targets:

| Block type | Target utilization |
|---|---|
| Random logic | 70–75 % |
| Datapath (regular) | 75–85 % |
| Memory wrapper | 60–70 % |

If RTL grows faster than expected, the area estimate that drove the
floorplan is wrong → utilization climbs → congestion follows.

**RTL responsibility:** estimate area accurately. Add safety margin for
DFT cell overhead (~5%), CTS buffer overhead (~5%), and timing-driven
upsizing (~10%).

### 2. Large flat macros

A wide mux (e.g., 64-bit 2:1 = 128 data inputs + 1 select + 64 outputs =
193 wires) concentrates 193 tracks at one location. The mux is a tiny
cell area-wise but a huge **pin density** spike.

**RTL alternatives:**

- **Pipeline the mux.** Two stages of 32-bit muxes each → half the pin
  density per location.
- **Slice it.** Replace one wide module with multiple narrow ones,
  placed apart.
- **Avoid full barrel shifters / huge adders.** Trade area for pipelining.

Same logic for wide adders, multipliers, CAMs, priority encoders. Pin
density is what matters, not gate count.

### 3. Composite macros (large boolean functions)

A single cell with many inputs realizing a wide boolean function looks
appealing (fewer levels of logic), but the many input wires must all
converge at one location. Local pin density spike again.

**Synthesis directive:** `set_size_only` or `set_dont_touch` on a target
cell prevents the synthesizer from merging logic into it. Or break up
the function in RTL so the synthesizer can't recombine.

### 4. Wide fanout

One driver feeding hundreds of destinations needs:

- Buffer tree (consumed area) — and
- Wires from each tree leaf to its destination (consumed tracks).

Destinations are physically scattered → long wires → many tracks
occupied → congestion.

**RTL alternatives:**

- **Pipeline the high-fanout signal.** Register-replicate so each copy
  drives a smaller fanout. Sets of identical flops, hint to synthesizer
  with `register_replication` directive.
- **Avoid status flags reaching every block.** Slot them onto a status
  bus that's only read on demand.
- **Don't broadcast clock-gate enables.** Localize the gating closer to
  the gated logic.

### 5. Wide fanin cone

The mirror image: one register's `D` driven by a wide cone of
combinational logic. Every input to that cone must route to the cone's
gates, then converge on the destination flop. Convergence point is the
hot spot.

**RTL fix:** pipeline the cone. Insert a pipeline register, splitting
the fanin into two narrower cones with a flop boundary in between.

### 6. Too many critical paths

Critical paths (paths near the timing target) must route through the
*shortest* available route — they can't detour. If many paths are
critical, the router has no flexibility to route around congestion.

```
[fig 8.3a] Healthy timing — few critical paths, fat slack tail
[fig 8.3b] Bad timing — many paths at the cliff, all need shortest route
```

**RTL fix:** retiming, pipelining, and area-budget slack on
non-critical paths so the router can use detours.

### 7. Hard-macro placement and feedthroughs

A hard macro (already-routed IP) is an opaque blockage to the router.
Signals trying to cross from one side to the other must detour around
it — high congestion in the macro's vicinity.

**Macro-author responsibility:** include **feedthroughs** — straight
input-to-output wires through the macro that have no logic, just metal.
These let signals pass through the macro's body instead of routing
around its edges.

(Note: "feedthrough" here is a physical-design term. The unrelated RTL
"feedthrough" — data overshooting a register stage in one cycle — is in
`clean-rtl/references/feedthrough.md` if added.)

## RTL coding patterns to prefer

- **Many small modules with narrow interfaces** > one big flat module.
  Modular hierarchy gives the floorplanner natural cut lines.
- **Locality of reference.** Signals used together should be defined
  together; the synthesizer keeps related logic local.
- **Register the boundaries of large blocks.** Pipeline registers at
  block interfaces give the floorplanner placement freedom.
- **Avoid registers in clouds.** A `for-generate` instantiating 256 flops
  in a single module is a placement hot spot. Split.
- **Hierarchical clock gating.** Coarse gating high in hierarchy + finer
  gating at the leaves spreads enable-signal fanout.

## RTL anti-patterns

| Anti-pattern | Why it congests | Better RTL |
|---|---|---|
| 64-bit wide muxes inline | Pin density spike | Pipeline mux, slice |
| Status-flag broadcast to every block | Wide fanout | On-demand status bus |
| Big arithmetic in a `always_comb` | Wide fanin cone | Multi-stage pipeline |
| Dense `for-generate` of 256 flops in one place | Local utilization | Split across modules |
| One huge boolean function per cycle | Composite-macro effect | Multi-cycle path + smaller stages |
| `dont_touch` on a wide net | No buffer-tree relief | Allow synth to buffer; replicate at RTL |

## How to spot it pre-placement

Tools that estimate congestion before P&R:

- **Synthesis QoR reports** — pin density per region, after `placeopt`.
- **RTL Compiler / Genus `report_congestion`** — flags pin-density hot
  spots from the synthesis netlist.
- **Synopsys IC Compiler `report_congestion -route_estimate`** —
  early placement-driven estimate.
- **PrimePower / Synopsys Activity reports** — high-activity nets often
  correlate with high routing demand on those nets.

For RTL-level pre-checks:

- Lint for wide muxes (>16 entries).
- Lint for `assign` cones with > N levels.
- Module-level pin count thresholds (warn if a module has > 200 ports).
- Reuse the synthesis `area-time` graph — if many paths sit at the
  timing cliff, expect congestion.

## Examples

### Bad

```systemverilog
// 64:1 mux — 64 data inputs + 6 sel + 1 out = 71 wires converging
always_comb
    case (sel)
        6'd0:  out = in[0];
        6'd1:  out = in[1];
        // …
        6'd63: out = in[63];
        default: out = '0;
    endcase
```

### Better (pipelined, two stages)

```systemverilog
// Stage 1: eight 8:1 muxes
logic [7:0][W-1:0] mux1_out;
always_comb begin
    for (int i = 0; i < 8; i++)
        mux1_out[i] = in[i*8 +: 8][sel[2:0]];
end

logic [7:0][W-1:0] mux1_reg;
always_ff @(posedge clk) mux1_reg <= mux1_out;

// Stage 2: 8:1 mux on the registered output
always_comb out = mux1_reg[sel[5:3]];
```

Same function, one cycle of latency added, congestion massively reduced.

## Citations

- **Churiwala & Garg**, *Principles of VLSI RTL Design*, §8 — RTL
  characteristics that drive routing congestion, with figures and
  remediation.
- **Cadence Innovus User Guide** — `report_congestion`, pin-density
  metrics.

## See also

- `rtl-coding-for-synthesis.md` — synthesis-friendly RTL baseline.
- `timing-optimization.md` — pipelining and retiming techniques.
- `synthesis-attributes.md` — `register_replication`, `dont_touch`,
  `size_only`.
- `dft-patterns` skill — DFT cells add ~5% to utilization budget.
