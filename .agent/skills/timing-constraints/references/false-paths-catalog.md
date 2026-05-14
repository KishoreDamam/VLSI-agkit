# False Paths — Eight-Category Catalog

> When to declare a path false, what command to use, and what the risk is.
> A path declared false is a path with *no upper bound on delay* — get the
> declaration wrong and silicon fails.

## Big-picture decision

```
Path between two clocks?  ─── async? ───── set_clock_groups -asynchronous (preferred)
                          │                or set_false_path (legacy)
                          │
                          └── exclusive? ── set_clock_groups -physically_exclusive
                                            (clock mux: only one active at a time)
                                            or -logically_exclusive
                                            (mode-driven: never both selected)

Path through a structurally connected but never-functional cone?
                          ─── set_false_path -from/-through/-to

Quasi-static signal (config reg, test-mode select)?
                          ─── set_false_path -from <signal>

Async control signal (assert side)?
                          ─── set_false_path -from rst_n -fall (or -rise per polarity)
                              (de-assertion side still needs recovery/removal check)

Multi-mode path that exists only in one mode?
                          ─── set_case_analysis (preferred, scopes correctly)
                              or set_false_path between mode-specific clocks

Pin-muxed output (two different clocks drive the same port)?
                          ─── Declare virtual clocks per mode, false-path real↔virtual
                              cross-pair (real_clk1 → vclk2 and vice-versa)
```

## Category 1 — Protocol-only paths

Two peripherals share a bus through a master. Structurally, peripheral 1
can drive peripheral 2 via the master pin; functionally, the protocol
prohibits it (master mediates every transfer).

```tcl
set_false_path -from [get_clocks p1_clk] -to [get_clocks p2_clk]
set_false_path -from [get_clocks p2_clk] -to [get_clocks p1_clk]
```

Risk: low. Protocol guarantees the path is unused.

## Category 2 — Unsensitizable paths

The path exists structurally but no input vector can propagate a
transition through it. Common synthesis-induced shapes:

- A mux with constant select that the synthesizer didn't optimize away.
- A reconvergent fanout where the two branches have opposite unateness
  — transitions cancel at the merge.

```tcl
set_false_path -from <pin_b> -to <pin_e>
```

Risk: **moderate**. The path is functionally inert, but *glitches* on
the differential delay can still produce a glitch at the merge. If that
merge feeds a flop D pin, the glitch can be captured. Audit the cone
before declaring; consider letting the path stay timed instead.

## Category 3 — Clock-domain crossing paths

Async CDC paths cannot be timed deterministically — the relationship
between launch and capture clocks is unknown.

```tcl
# Preferred
set_clock_groups -asynchronous \
    -group [get_clocks src_clk] \
    -group [get_clocks dst_clk]

# Legacy / equivalent
set_false_path -from [get_clocks src_clk] -to [get_clocks dst_clk]

# Bounded alternative (better for routing, prevents extreme delays)
set_max_delay <dst_period> -datapath_only \
    -from <src_reg/Q> -to <dst_sync_reg/D>
```

Risk: **high if structural sync is missing**. False-path means *no*
timing on the CDC; without a 2-FF (or async-FIFO) synchronizer at the
destination, the device fails in silicon. STA gives no warning here —
CDC tool (Spyglass CDC, Questa CDC) must run separately.

`set_clock_groups` is preferred over `set_false_path` because:

- Conveys *intent* (these are async domains).
- Cross-talk analysis treats them correctly (no SI between async clocks).
- Implies the symmetric direction (one declaration covers both ways).

## Category 4 — Multi-mode paths (scan vs functional)

Same clock pin, two modes, two effective periods. During functional mode
the clock runs at 10 ns; during scan-shift at 40 ns. Without
mode-scoping, every scan-path path appears in the functional analysis.

**Preferred**: declare `set_case_analysis` on the mode-select signal so
the engine analyzes only the active mode at a time:

```tcl
create_clock -name FuncClk -period 10 [get_ports clk1]
set_case_analysis 0 [get_ports ScanEn]   ;# functional mode
```

For a combined SDC that covers both modes simultaneously:

```tcl
create_clock -name FuncClk -period 10 [get_ports clk1]
create_clock -name TestClk -period 40 [get_ports clk1]

set_false_path -from [get_clocks FuncClk] -to [get_pins *_reg/SI]
```

This false-path says: "any path from FuncClk to a scan-input pin is not
of interest." The reverse direction (TestClk → reg/D) is usually
omitted — it'll meet TestClk's 40 ns automatically.

Risk: **moderate**. Two clocks on one pin is intrinsically fragile;
prefer the case-analysis form when the flow supports it.

## Category 5 — Pin-muxing (shared I/O port)

An output pin carries data from F1 in one mode and from F2 in another;
each is captured by its corresponding clock externally. STA naturally
times *all four* sender/receiver pairings; only two are real:

```tcl
# 1. F1 launches, clk1 captures — real
# 2. F1 launches, clk2 captures — false
# 3. F2 launches, clk1 captures — false
# 4. F2 launches, clk2 captures — real

# Declare virtual clocks for the external receiver
create_clock -name vclk1 -period 10
create_clock -name vclk2 -period 12

set_output_delay 1.0 -clock vclk1 [get_ports out]
set_output_delay 1.0 -clock vclk2 [get_ports out] -add_delay

# Exclude the cross-pair (real launch → wrong virtual capture)
set_false_path -from [get_clocks clk1] -to [get_clocks vclk2]
set_false_path -from [get_clocks clk2] -to [get_clocks vclk1]
```

Risk: low when paired with virtual clocks. **High** if you false-path
the real clocks directly (`clk1 ↔ clk2`) — that silently kills any
internal interaction between the two clocks.

## Category 6 — Exclusive clocks (mux'd clocks)

A mux selects between two clocks; only one reaches the flop at a time.

```
       clk1 ─┐
             │
         M1 ─┴─→ flop CK
             │
       clk2 ─┘
```

If no flops sit *upstream of the mux* on either clock:

```tcl
set_clock_groups -physically_exclusive \
    -group [get_clocks clk1] \
    -group [get_clocks clk2]
```

**Trap.** If a flop *is* clocked directly by clk1 or clk2 before the mux,
that flop launches into a register downstream of the mux — which gets
the *other* clock. False-pathing clk1↔clk2 would mask that real path.

**Fix.** Create generated clocks at the mux inputs and apply exclusivity
to the *generated* clocks only:

```tcl
create_generated_clock -name gclk1 -combinational \
    -source [get_ports clk1] -master_clock [get_clocks clk1] \
    [get_pins M1/A]
create_generated_clock -name gclk2 -combinational \
    -source [get_ports clk2] -master_clock [get_clocks clk2] \
    [get_pins M1/B]

set_clock_groups -physically_exclusive \
    -group [get_clocks gclk1] -group [get_clocks gclk2]
```

Risk: **high** if exclusivity is applied to root clocks instead of
generated post-mux clocks. Re-audit after every netlist change.

## Category 7 — Async control signals

Reset and similar signals assert asynchronously and stay asserted across
many cycles. **Assertion** doesn't need timing — every flop will see it
within "enough" cycles. **De-assertion** still needs recovery/removal
checks because all flops must come out of reset on the *same* edge.

```tcl
# Don't time assertion (active-low reset, falling edge)
set_false_path -from [get_ports rst_n] -fall

# Or with set_multicycle_path as a soft upper bound
set_multicycle_path 4 -setup -from [get_ports rst_n] -fall
```

Even on the assertion side, the safer pattern is a multi-cycle (some
upper bound) rather than a true false-path (unbounded).

## Category 8 — Quasi-static signals

Configuration registers, test-mode pins, clock-divide ratios — written
once at boot and held thereafter. The fanout cone never sees a
transition during normal operation.

```tcl
set_false_path -from [get_cells cfg_reg*/*]
```

Risk: **low** *if* the signal really is static after boot. Audit every
year — designs that started as static often grow runtime-updatable
config registers, at which point the false-path becomes a silicon bug.

## Common mistakes that break silicon

- **False-path between two synchronous registers** that just happens to
  fail timing — you've masked a real bug.
- **False-path on the assertion *and* de-assertion of reset** — the
  de-assertion can race and put some flops into different cycles of
  reset exit.
- **`set_false_path -from clk1 -to clk2` for an async CDC that has no
  synchronizer** — STA is happy; silicon eats a metastability bug.
- **`-physically_exclusive` on root clocks** when a flop intervenes
  before the mux (see Category 6).
- **Multicycle hold-side forgotten** when the false-path was actually
  meant to be a multicycle. See `multicycle-paths.md`.

## `set_false_path` vs `set_clock_groups` — when to use which

| | `set_false_path` | `set_clock_groups` |
|---|---|---|
| Timing impact | Skip the path | Skip the path |
| Intent communication | "Don't time this path" | "These clocks are async / exclusive" |
| SI / crosstalk analysis | May still analyze | Excluded correctly |
| Symmetric (both directions) | Need two commands | One command covers both |
| Granularity | Per path (with -from/-to/-through) | Per clock group only |
| SDC version | Always available | SDC 1.7+ |

**Default:** `set_clock_groups` when the unit of analysis is a clock pair;
`set_false_path` for path-level exceptions (e.g., quasi-static).

## Sign-off review checklist

- [ ] Every `set_false_path` has a comment naming one of the 8 categories.
- [ ] Every `set_clock_groups` lists the right group type (async,
      physically_exclusive, logically_exclusive).
- [ ] No false-path crosses a structural synchronous register pair.
- [ ] CDC tool run independently of STA — no false-path entry assumed to
      replace a synchronizer.
- [ ] Reset false-paths qualified by `-rise`/`-fall` if only one edge
      should be excepted.
- [ ] Quasi-static false-paths re-validated against current RTL (the
      "static" signal didn't grow runtime updates).
- [ ] `set_clock_groups` applied to *generated* clocks where a clock-mux
      precedes a flop on each leg (Category 6).

## Citations

- **SDC 1.9** — `set_false_path`, `set_clock_groups`, `set_case_analysis`,
  `set_max_delay -datapath_only`, virtual clocks.
- **Churiwala & Garg**, *Principles of VLSI RTL Design*, §7.1 —
  eight-category framing reproduced above.

## See also

- `multicycle-paths.md` — when a path needs *more* time, not none.
- `clock-declarations.md` — `create_generated_clock` for mux'd-clock
  cases.
- `sta` skill `references/crpr.md` — CRPR behavior across these
  exception types.
- `clock-domain-crossing` skill — structural sync that STA exceptions
  do not replace.
