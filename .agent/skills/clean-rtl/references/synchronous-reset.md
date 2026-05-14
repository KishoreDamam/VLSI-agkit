# Synchronous Reset — Coding Style

> Synthesizers can recognize a synchronous reset *only* if the RTL is shaped
> a certain way. Sub-optimal shapes produce functionally equivalent but
> physically inferior netlists.

## Two reset families

| | Async reset | Sync reset |
|---|---|---|
| Sensitivity | `posedge clk or negedge rst_n` | `posedge clk` only |
| Pin used | Library async clear/preset | Data pin (via mux logic) |
| Power-on behavior | Reset asserted before clock starts | Needs clock running |
| Glitch sensitivity | Async net can glitch and reset | Sync — glitch must meet setup |
| ASIC bias | Common (especially for high-rel) | Used for sub-block resets |
| FPGA bias | Async risky on Xilinx — recommend sync | Vendor-preferred |

This reference is about **synchronous reset coding**. Async reset is a
separate topic (see project conventions).

## Why coding shape matters

For synchronous reset, the synthesizer has a choice:

- Map the reset signal to a **dedicated sync-clear pin** of the flop
  library cell (if the cell library exposes one) — minimal logic, reset
  is physically close to the flop.
- Or **build the reset as combinational logic** in front of the flop's D
  pin — extra gates, reset goes through ordinary data routing.

Only the first option is what you want. To get it, the synthesizer must
*recognize* that a particular signal is "the reset," and that requires:

1. The RTL must structurally identify the reset signal (first `if`
   condition in the clocked block).
2. The synthesizer must be told this signal is sync-reset (via a pragma
   or attribute, or by recognizing the canonical idiom).

## The canonical idiom

```systemverilog
// pragma synthesis_off
// pragma synthesis_on

//synopsys sync_set_reset "rst_n"
always_ff @(posedge clk) begin
    if (!rst_n)     q <= 1'b0;     // sync reset — first if
    else            q <= d;        // data — in else
end
```

Rules:

1. **First `if` is the reset check.** Always `if (!rst_n)` (active-low)
   or `if (rst)` (active-high). One condition, evaluating a single signal.
2. **Reset asserts to the inactive value.** The reset branch assigns
   constant 0 (or 1 for preset). No data, no logic.
3. **`else` holds the data path.** Everything that is not reset goes in
   the `else`.
4. **`synopsys sync_set_reset` pragma** for Synopsys DC. Other tools
   have analogous mechanisms; consult the synthesis flow guide for the
   exact incantation (Genus uses `set_db / -set / -reset` attributes).

## Forms that don't get recognized

All of these produce the same simulation behavior. Most produce the same
*logical* netlist. None get the dedicated sync-clear pin.

```verilog
// ❌ Reset symmetric with data — synthesizer can't tell which is "reset"
always_ff @(posedge clk)
    q <= d & rst_n;

// ❌ Reset constructed outside the always block
assign next_q = d & rst_n;
always_ff @(posedge clk)
    q <= next_q;

// ❌ Reset as one case branch — recognized by some tools, not all
always_ff @(posedge clk)
    case (rst_n)
        1'b0: q <= 1'b0;
        1'b1: q <= d;
    endcase
```

Each of the above will synthesize, simulate, and pass functional checks.
The realized circuit puts an AND gate (or mux) in front of the flop
instead of using the flop's sync-clear pin. Difference shows up as:

- Higher cell count (one extra gate per reset target).
- Worse setup margin on `rst_n` (extra delay on the reset path).
- Worse hold margin on `d` (data path has one more gate).
- DFT-tool may misclassify the reset, causing unnecessary scan
  constraints.

## Register-inference report — verify recognition

Synopsys DC produces a register-inference report after compile. Each
flop shows columns:

```
| Reg Name | Type      | Width | Bus | MB | AR | AS | SR | SS | ST |
| q_reg    | Flip-flop | 1     | N   | N  | N  | N  | Y  | N  | N  |  ← SR=Y means sync reset recognized
```

| Column | Meaning |
|---|---|
| AR | Async Reset |
| AS | Async Set |
| SR | **Sync Reset** ← what you want for sync designs |
| SS | Sync Set |
| ST | Sync Toggle |
| MB | Multi-Bit |

`SR=Y` is the signal that the sync-clear pin was used. `SR=N` on a
register that should have sync-reset means the synthesizer didn't
recognize the idiom — go back and fix the RTL or the pragma.

Genus and Vivado have equivalent reports — different column names but
the same meaning.

## Combined async + sync reset (less common, but real)

When a block has both an async POR and a sync soft-reset:

```systemverilog
always_ff @(posedge clk or negedge async_rst_n) begin
    if (!async_rst_n)        q <= 1'b0;    // async POR — most dominant
    else if (!sync_rst_n)    q <= 1'b0;    // sync soft-reset — secondary
    else                     q <= d;
end
```

Both branches map to the appropriate library pins (async-clear *and*
sync-clear), provided the pragma identifies both.

## When a sync-clear flop isn't available

Some library variants (low-power, high-Vt, low-area) skip the sync-clear
pin. The synthesizer then builds the reset logic out of an AND/mux as
above — and may flag a warning. Options:

- **Live with it** — extra gate per reset target; usually acceptable.
- **Force a different library cell** — `set_dont_use` on the non-SR
  variant, or `set_size_only` on a hand-instantiated DFF with SR.
- **Switch to async reset for this domain** — if the design allows it.

## Common pitfalls

- **Reset polarity inconsistency.** Half the project uses active-low
  `rst_n`, half uses active-high `rst`. Mix breaks recognition and adds
  inverters. Pick one project-wide.
- **Reset assertion not constant.** `if (!rst_n) q <= d_at_reset_time;`
  is not a reset — it's just a clocked mux. Reset branches must assign
  constants (or known parameters).
- **Multiple resets via cascaded `if/else if`.** Works if order is
  intentional (most dominant first), but synthesizers may reject more
  than 2 levels — read the warnings.
- **Forgetting the pragma on tools that need it.** Without
  `sync_set_reset`, even the canonical idiom can fail recognition on
  some library/tool combinations.
- **Reset signal in two clock domains.** Treat the sync-reset like any
  CDC signal — synchronize it into the destination domain before use.
  See `clock-domain-crossing` skill.

## Citations

- **Churiwala & Garg**, *Principles of VLSI RTL Design*, §2.6 —
  sync-reset coding idiom and register-inference reports.
- **Synopsys Design Compiler User Guide** — `sync_set_reset` pragma.
- **Cummings**, *"Synthesis and Scripting Techniques for Designing
  Multi-Asynchronous Clock Designs,"* SNUG 2001 — reset domain crossings.

## See also

- `simulation-race.md` — initial-always race involving reset.
- `latch-inference.md` — reset paths can accidentally infer latches if
  the `else` is missing.
- `clock-domain-crossing` skill — resets that cross domains need
  synchronizers.
