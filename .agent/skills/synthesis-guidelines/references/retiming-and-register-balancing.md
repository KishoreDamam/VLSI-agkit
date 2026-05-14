# Retiming and Register Balancing

> Synthesis can *move* flip-flops across combinational logic to even out
> stage delays. The optimization is automatic, but specific RTL patterns
> turn it off — silently. This reference explains the distinction between
> pipelining, retiming, and register balancing, and the trap patterns that
> disable them.

## The three optimizations — same family, slightly different

| | Pipelining | Retiming | Register balancing |
|---|---|---|---|
| What it does | Identifies a regular pipeline shape and redistributes flops along it | Moves a single flop forwards or backwards across logic | Generalized retiming applied to non-regular structures |
| Typical target | Pipelined multiplier, FIR | Arbitrary 2-stage flop pairs | Any flop chain |
| Adds / removes flops | No — only moves them | No | No |
| Changes latency | No | No | No |

The boundary between these terms is fuzzy and varies by tool. Treat them
as different *names* the same vendor uses for slightly different
strengths of the same underlying graph transformation:

```
Before retiming:                After retiming:

   ──[LOGIC A: 1ns]──[flop]──[LOGIC B: 5ns]──[flop]──
                                                       
                          ↓

   ──[LOGIC A: 3ns]──[flop]──[LOGIC B: 3ns]──[flop]──
```

The total combinational delay (6 ns) and total flop count (2) are
unchanged. But the *worst* stage delay drops from 5 ns to 3 ns — Fmax
improves.

## When retiming helps and when it doesn't

### Helps when

- The critical path is imbalanced: one stage is much slower than
  adjacent stages.
- The same module is reused; pushing flops in/out yields better timing
  on every instance.
- Synthesis is told the constraint and has slack on the *easy* stage to
  borrow against.

### Doesn't help when

- Paths are already balanced — no slack to move around.
- Reset-type asymmetry blocks the move (see below).
- Synchronizer registers are involved (see below).
- The critical path is in a hard macro the synthesizer can't enter.

A smart synthesis tool only applies retiming to paths that need it.
Forcing global retiming wastes runtime on already-balanced paths.

## Trap 1 — Mixed reset types prevent retiming

If two adjacent flops have *different reset behaviour* (one sync, one
async; or one set, one reset; or one resetable, one not), the
synthesizer cannot retime across them — they cannot be combined or
re-aligned.

```systemverilog
// ❌ Mixed reset types — retiming blocked
always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) a_q <= 0;
    else        a_q <= a_in;

always_ff @(posedge clk)         // sync (no reset clause)
    b_q <= a_q;

// Synthesizer cannot push logic across the a_q→b_q boundary
// because a_q has async reset semantics and b_q has none.
```

**Fix:** make all flops in a pipeline use the same reset style. The
canonical pattern:

```systemverilog
// ✅ Consistent reset style — retiming works
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        a_q <= 0;
        b_q <= 0;
    end else begin
        a_q <= a_in;
        b_q <= a_q;
    end
end
```

A smart synthesizer may *try* to work around mixed resets by inverting
through the boundary (XOR-trick), but it's expensive and usually
unsuccessful. Audit your reset coverage; mismatch is the most common
silent retiming blocker.

## Trap 2 — Synchronizers must be protected

A CDC synchronizer (`a_meta → a_sync_q1 → a_sync_q2`) relies on
*not* having any combinational logic between the two flops.
Retiming would happily push logic into that gap, which destroys MTBF.

```systemverilog
// CDC 2-FF synchronizer
always_ff @(posedge clk_dst) begin
    a_meta    <= a_async;       // metastable
    a_sync_q1 <= a_meta;        // first sync register
    a_sync_q2 <= a_sync_q1;     // second sync register — output
end

// Downstream uses a_sync_q2 to drive complex logic
always_ff @(posedge clk_dst)
    decoded <= big_complex_function_of(a_sync_q2);
```

If retiming pushes `big_complex_function_of` into the gap between
`a_sync_q1` and `a_sync_q2`, the second flop now sees post-logic data
— but the metastability window of the first flop hasn't necessarily
closed yet. Silicon MTBF collapses.

**Fix:** annotate synchronizer registers with a vendor attribute that
disables retiming on them:

```systemverilog
// Xilinx
(* ASYNC_REG = "TRUE", DONT_TOUCH = "TRUE" *) reg a_sync_q1;
(* ASYNC_REG = "TRUE", DONT_TOUCH = "TRUE" *) reg a_sync_q2;

// Intel
(* preserve, dont_replicate *) reg a_sync_q1;
(* preserve, dont_replicate *) reg a_sync_q2;
```

Some flows accept a generic `keep` or `syn_keep` attribute. Check the
synthesis log: the attribute should appear in the cell properties of
the synthesized netlist. If it's silently stripped, retiming will
proceed.

## Trap 3 — Don't retime across a multicycle path boundary

A path declared with `set_multicycle_path` runs at a slower effective
rate. The synthesizer sees more slack and may retime aggressively.
After retiming, a flop now sits *inside* what was a multicycle path —
splitting it into two single-cycle paths. The multicycle constraint no
longer means what it did.

**Fix:** use `set_dont_touch` or `set_size_only` on the source/sink
registers of multicycle paths. Or scope the multicycle to specific
cell names that retiming won't change.

## Pipelining a regular structure

Pipelining (the most-restricted form) needs a recognizable shape:

```systemverilog
module multpipe #(parameter W = 8, parameter D = 3) (
    output [2*W-1:0] o_prod,
    input  [W-1:0]   i_in1, i_in2,
    input            i_clk
);
    reg [2*W-1:0] prod_reg [D-1:0];

    always_ff @(posedge i_clk) begin
        prod_reg[0] <= i_in1 * i_in2;
        for (int i = 1; i < D; i++)
            prod_reg[i] <= prod_reg[i-1];
    end

    assign o_prod = prod_reg[D-1];
endmodule
```

A direct mapping places `i_in1 * i_in2` in front of one flop, with all
subsequent flops idle. The pipelining optimization recognizes the
shift-register chain and *pushes the multiplier deeper into the
pipeline* — distributing the multiplier's combinational delay across
the D stages.

Result: same latency (D cycles), same area, much higher Fmax.

Vendor switches:

```tcl
# Xilinx Vivado
set_property STEPS.SYNTH_DESIGN.ARGS.RETIMING true [get_runs synth_1]

# Synopsys DC
compile_ultra -retime

# Genus
syn_generic -effort high
syn_map     -effort high
```

## Resource sharing — adjacent optimization, similar caveats

Synthesis can merge mutually-exclusive arithmetic operators:

```systemverilog
// Two adders with a selector
assign o_dat = i_sel ? i_dat1 + i_dat2 : i_dat1 + i_dat3;
```

Direct mapping: two adders, output mux. Resource-shared: one adder, input
mux. Area drops. Timing **may** worsen because the muxes are now on the
critical path (mux delay + adder delay > adder delay + mux delay).

**Rule:** enable resource sharing globally; verify the critical path
post-synth. If a shared resource shows up on the WNS, force `dont_touch`
on the operator instances on that path.

## Speed-vs-area trade-off and over-constraining

Setting a tighter timing constraint than the design can achieve is a
classic mistake. Synthesis must commit to a logic topology before it
knows the post-place utilization. With an unreachable target it
sometimes:

- Trades area aggressively for parallelism → over-utilization →
  congestion → worse Fmax than a relaxed constraint.
- Gives up early ("design will not meet timing") and produces a
  pessimistic, unbalanced netlist.

```
       Achieved
       Fmax │
            │        ╭───── peak
            │       ╱
            │      ╱  ← optimization region
            │     ╱
            │────╯
            │ underconstrained        overconstrained
            └────────────────────────────────────
              Constraint target
```

Rule of thumb: target Fmax + 15–20 % headroom. Beyond that, drops back.
Under-constrain (or no constraint) → compact, slow design. Optimal
constraint → headroom that lets the synth tool experiment.

## Debugging retiming behaviour

```tcl
# Vivado
report_property [get_cells my_flop_q]    ;# shows DONT_TOUCH, KEEP, ASYNC_REG attrs
report_methodology -severity {CRITICAL WARNING}

# Synopsys DC
report_attributes -application -class cell [get_cells *]

# Intel Quartus
analyze_settings -section RETIMING
```

If your design has imbalanced paths but retiming "doesn't help":

1. Check reset uniformity across the failing path.
2. Check for `DONT_TOUCH` / `KEEP` attributes (especially auto-inserted
   on synchronizers).
3. Check the multicycle / false-path exception list — retiming respects
   those.
4. Verify the synthesis switch is actually enabled (the global option
   may be off, or per-module attributes may override it).

## Common pitfalls

- **Mixed reset across pipeline stages**, silently blocks retiming
  across the design.
- **Synchronizer registers without `ASYNC_REG`** — retiming destroys
  MTBF.
- **Multicycle path boundary retimed through**, multicycle no longer
  applicable.
- **`set_dont_touch` on the whole module** when only one register
  needs protection — turns off all optimization including legitimate
  retiming.
- **DDR-register I/O retimed into general fabric** — vendor-specific
  primitives have placement constraints; retiming moves them out of
  the I/O ring.
- **Resource sharing breaks critical path** — verify post-synth.
- **Over-constraining the timing target** — synthesis gives up; produces
  worse design than the relaxed target.

## Citations

- **Kilts**, *Advanced FPGA Design*, Wiley 2007, Chapter 14 — speed vs
  area, retiming, register balancing, resource sharing.
- **Xilinx UG901** — Vivado Synthesis user guide, retiming directives.
- **Synopsys Design Compiler User Guide** — `compile_ultra -retime`.

## See also

- `rtl-coding-for-synthesis.md` — RTL patterns that survive retiming.
- `synthesis-attributes.md` — `dont_touch`, `keep`, `async_reg`,
  `preserve`.
- `fsm-compilation-and-encoding.md` — related synthesis transform on
  state machines.
- `clock-domain-crossing` skill — synchronizer structure that retiming
  must preserve.
