# Multicycle Paths Reference

## Conceptual model

By default, STA requires every combinational path to complete within one clock
cycle (1 × period). A multicycle path relaxes that requirement to N cycles for
setup, which is correct when the destination register intentionally latches only
every Nth clock edge.

**Setup analysis window:** the tool checks that data launched at cycle k arrives
before the Nth capture edge (k + N). Relaxing setup by N means the path has
N × period to complete instead of 1 × period.

**Hold analysis window:** after relaxing setup to N cycles, the default hold
check shifts to the (N−1)th capture edge. This means the tool checks that data
launched at cycle k does not arrive too late to be held at cycle k + N − 1.
In practice, hold is now checked at an edge that is N−1 cycles later than the
default, which is too lenient — data from cycle k+1 launch could collide.

**The fix:** always add a compensating `set_multicycle_path N-1 -hold` to move
the hold check back to the correct edge.

---

## N=3 Concrete Example

Design intent: an ALU result is registered by a slow pipeline stage; the
destination register's enable is asserted every 3rd clock cycle.

```
Cycle:    0    1    2    3    4    5    6
Launch:   ↑              ↑              ↑
Capture:            ↑              ↑
          |←  3 cycles →|    (setup window)
```

```tcl
# Relax setup: path has 3 × period instead of 1 × period
set_multicycle_path 3 -setup \
    -from [get_cells alu_*/Q] \
    -to   [get_cells result_*/D]

# Compensate hold: shift hold check back by N-1 = 2 cycles
# Without this, the tool checks hold N-1=2 cycles too late,
# allowing data from a later launch to corrupt the capture.
set_multicycle_path 2 -hold \
    -from [get_cells alu_*/Q] \
    -to   [get_cells result_*/D]
```

### Why the hold compensation is mandatory

After the `set_multicycle_path 3 -setup` command, the tool moves the setup
capture edge to cycle +3. The default hold check is performed one cycle before
the setup capture edge, which is now cycle +2 instead of cycle 0.

A new data value launched at cycle +1 could reach the destination by cycle +2
and overwrite the data that was supposed to be captured at cycle +3. Without
the `-hold` compensation, the tool does not flag this scenario.

`set_multicycle_path 2 -hold` moves the hold check back to its original
position (cycle 0 relative to launch), preventing the tool from missing the
real hold violation window.

**Rule:** For any `set_multicycle_path N -setup`, always add
`set_multicycle_path N-1 -hold` with identical `-from`/`-to` scope.

---

## `set_false_path` vs `set_multicycle_path` for Static Signals

A register written once at boot and held static for the remainder of operation
can be constrained two ways:

| Approach | Command | Tradeoff |
|---|---|---|
| Remove from analysis entirely | `set_false_path -from [get_cells cfg_reg*/Q]` | Tool places no routing constraint; synthesis may not optimize for delay. Safe only if signal is truly static and never changes during operation. |
| Relax setup generously | `set_multicycle_path 4 -setup -from [get_cells cfg_reg*/Q]` | Path still has a routing budget (4 × period); synthesis and P&R still optimize within that budget. Preferred when the signal might be updated during a safe reconfiguration window. |

**Recommendation:** Use `set_false_path` for permanently static signals
(constants, straps, OTP-derived configuration) where no timing analysis is
ever meaningful. Use `set_multicycle_path` when the signal could change during
known safe windows (e.g., during a reset sequence) — the generous budget
prevents timing violations while keeping synthesis honest.

---

## From/To Scope

`set_multicycle_path` applies to all paths between the `-from` and `-to`
collections. Scope too broadly and you may accidentally cover critical paths.
Scope too narrowly and violations reappear.

```tcl
# Scope by cell name pattern
set_multicycle_path 2 -setup -from [get_cells slow_path_*/Q] \
                              -to   [get_cells result_reg*/D]

# Scope by net (useful for specific bus)
set_multicycle_path 2 -setup -from [get_nets slow_data*] \
                              -to   [get_cells result_reg*/D]
```

Always run `report_exceptions` after adding multicycle constraints and verify
the path count matches your expectation — an overly broad glob is a common
source of masked violations.

---

## Interaction with Clock Period

Multicycle N means N × source_period for same-frequency paths. For
cross-frequency paths (source clock ≠ destination clock), the tool uses the
common clock period (LCM or the more conservative of the two). Inspect
`report_timing` to confirm the actual analysis window being used.

---

## Common Mistakes

| Mistake | Effect | Fix |
|---|---|---|
| Omitting `-hold` companion | Hold violations at destination FF; may fail in silicon | Always pair with `set_multicycle_path N-1 -hold` |
| Setting `-hold` to N instead of N-1 | Over-constrains hold; false hold violations | Use N-1 for `-hold` |
| Using `set_false_path` on a signal that can change | Synthesis ignores timing; real violations masked | Use `set_multicycle_path` with a generous N instead |
| Scope covers both critical and non-critical paths | Critical path accidentally relaxed | Narrow scope using explicit cell names or hierarchical path |
