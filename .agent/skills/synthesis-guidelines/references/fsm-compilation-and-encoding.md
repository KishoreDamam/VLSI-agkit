# FSM Compilation and State Encoding

> Synthesis recognizes finite state machines coded in standard patterns
> and can recode them automatically for the target technology. This
> reference covers when the recognition fires, what encoding the tool
> picks, and which encoding *you* should ask for.

## FSM compilation — the synthesis transform

A finite state machine coded in canonical form has three identifiable
parts:

- A **state register**.
- A **next-state function** (combinational, of state and inputs).
- An **output function** (combinational or registered, of state and/or
  inputs).

Synthesis recognizes the pattern and can:

- Detect the state set.
- Identify reachable vs unreachable states.
- Re-encode the state register to a more optimal encoding.
- Inject a *safe-state* recovery path for radiation-hardened designs.

This is more powerful than ordinary logic synthesis — the tool
*understands* the FSM structure rather than treating it as random
combinational + registered logic.

## What "canonical form" means

For the synthesizer to recognize the FSM, write it in the standard
two- or three-process style:

```systemverilog
// 1. State register
typedef enum logic [2:0] {IDLE, SETUP, RUN, DONE} state_t;
state_t state_q, state_d;

always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) state_q <= IDLE;
    else        state_q <= state_d;

// 2. Next-state logic
always_comb begin
    state_d = state_q;             // default: hold
    case (state_q)
        IDLE:  if (go)   state_d = SETUP;
        SETUP:           state_d = RUN;
        RUN:   if (done) state_d = DONE;
        DONE:            state_d = IDLE;
    endcase
end

// 3. Output logic (Moore — state-only)
assign valid = (state_q == DONE);
```

The synthesizer sees:

- Enum / parameter-named states → state set.
- `case` block driven by state register → transition table.
- Output expressions driven by `state_q` → Moore outputs.

Then it can re-encode `state_q` into any internal representation,
provided the external behaviour (inputs, outputs, latency) is
preserved. The original `[2:0]` width is just a hint.

See the [`fsm-design`](../../../skills/fsm-design/SKILL.md) skill for
the full canonical form variants and trade-offs.

## Three encodings the tool picks from

### Binary / sequential

States numbered sequentially (`IDLE = 0`, `SETUP = 1`, ...). Uses the
minimum number of bits (`ceil(log2 N)` for N states). Next-state logic
decodes a state, which costs `log2(N)`-wide AND gates.

**Best when:** N is large and logic is cheap, register area is
expensive. Common on ASICs.

### One-hot

One register per state; exactly one bit set. State register width = N
flops. Next-state logic doesn't need a state decoder — each transition
arc is `state[k]` AND-ed with the input condition.

**Best when:** registers are cheap and logic is expensive. Always
default on FPGAs — they're register-rich, and one-hot reduces the
critical path by eliminating the state-decode logic level.

**Trade-off:** N flops instead of `log2 N`. For an 8-state FSM, 8 flops
vs 3 — barely matters. For a 64-state FSM, 64 vs 6 — significant.

### Gray-coded

Adjacent states differ by exactly one bit. Width same as binary.
Next-state logic same complexity as binary (still needs a decoder).

**Best when:**

- The state register output drives **asynchronous logic** (combinational
  paths into a different clock domain, output ports to another chip).
  Race conditions during the transition are bounded because only one
  bit moves at a time.
- **Low-power** matters and state transitions are frequent. Single-bit
  change = minimum switching capacitance per transition.
- **Mixed CDC** — when an FSM state must be observed in a different
  clock domain, gray-coding the state register makes the multi-bit
  capture safe.

**Avoid for:** ordinary on-chip FSMs without async or low-power
constraints. Gray adds decode complexity without benefit.

## Which encoding to ask for

| Situation | Pick | Why |
|---|---|---|
| Default FPGA FSM | One-hot | Faster, no decode |
| Default ASIC FSM | Binary | Smaller, registers expensive |
| FSM output crosses domains | Gray | Race-free single-bit transitions |
| FSM is high-toggle / low-power | Gray | Single-bit switching |
| FSM has > 32 states on FPGA | Binary | One-hot flop count starts to hurt |
| Safety-critical / aerospace | Binary + safe-states | Need recovery from cosmic-ray bit flips |

Tell the synthesizer:

```tcl
# Xilinx Vivado
set_property FSM_ENCODING one_hot [get_cells {state_q_reg[*]}]

# Synopsys DC
set_attribute -name state_vector state_q "{IDLE SETUP RUN DONE}"
set_attribute -name encoding_style one_hot

# Genus
set_db / .syn_fsm_encoding_style one_hot
```

Most tools allow per-FSM override; the global default is usually
`one_hot` (FPGA) or `binary` (ASIC).

## Safe-state recovery (radiation-hardened FSMs)

Cosmic-ray events can flip flop state bits. A 4-state FSM encoded as
binary (2 bits) has all 4 codes used — any bit flip lands in a valid
state. But:

- A **one-hot** FSM with 4 states uses 4 of 16 possible codes; 12 are
  illegal. A bit flip likely lands in an illegal state.
- A **binary 5-state** FSM in 3 bits uses 5 of 8 codes; 3 are illegal.

Without protection, the FSM gets stuck in the illegal state.

**Safe-state mode** synthesizers (`SAFE_STATE` directive in Xilinx,
`-safe_implementation` in Quartus, `fsm_safe_state` in DC) add a
`default` arm that forces a known recovery state:

```systemverilog
always_comb begin
    state_d = state_q;
    case (state_q)
        IDLE:  if (go) state_d = SETUP;
        SETUP:         state_d = RUN;
        RUN:   if (done) state_d = DONE;
        DONE:          state_d = IDLE;
        default:       state_d = IDLE;   // ← safe-state recovery
    endcase
end
```

Tools also inject "auto-reset" logic that detects any unreachable code
and forces the FSM back to a known state.

**Use when:** aviation, medical, military, space. Has area/Fmax cost
(extra decode logic for the recovery path). Don't use by default — most
designs don't experience cosmic-ray bit flips often enough to justify
the area.

## Unreachable state removal

The synthesizer may detect that a particular state is never reachable
from any other state and remove it entirely. Saves area and
potentially Fmax.

If the FSM is *intentionally* unreachable for safety (you want the
recovery logic to *exist* even though normal operation doesn't reach
it), the synthesizer's removal defeats the purpose. Use the safe-state
directive to *force* retention.

## Async output rule (use Gray)

If any FSM output drives an asynchronous external pin or crosses to a
different clock domain (combinationally — not through a synchronizer),
the state register *must* be gray-encoded.

Reason: a multi-bit transition like binary `01 → 10` toggles both bits
simultaneously. Due to routing skew, one bit changes a few ps before
the other. The async observer briefly sees `00` or `11` — a phantom
state. If that phantom state drives a downstream decision, the silicon
fails.

Gray-encoded `01 → 11` toggles one bit only. The async observer sees
either the old state or the new state — never a phantom.

```systemverilog
// FSM output drives an external trigger pin (no synchronizer at receiver)
typedef enum logic [2:0] {
    OFF       = 3'b000,
    STARTING  = 3'b001,
    RUNNING   = 3'b011,    // Gray-coded — adjacent states differ by 1 bit
    STOPPING  = 3'b010,
    OFF_AGAIN = 3'b110
} gray_state_t;

assign external_trigger = (state_q == RUNNING);
```

Synthesizer needs to *keep* this encoding — apply `KEEP_FSM_ENCODING`
or equivalent attribute, otherwise the optimizer may re-encode away
your gray code.

## Common pitfalls

- **Coding the FSM as random `if/else if/else`** — synthesizer doesn't
  recognize the pattern, no FSM-specific optimizations apply, encoding
  attribute is silently ignored.
- **One-hot encoding asked for, but only 2 states.** Tool reverts to
  binary (or refuses). One-hot for ≥ 3 states.
- **Missing `default` arm + `one_hot` encoding.** Illegal codes have no
  defined transition; lint flags but synth may still optimize as if
  unreachable.
- **Outputs in same `always_ff` as state.** Some encoders can't re-encode
  if the output is combined with the state register write. Use separate
  `always_comb` for output decode.
- **Gray encoding requested but tool re-encodes to one-hot** by default.
  Force with `KEEP` / `keep_fsm_encoding`.
- **Safe-state always on, even for non-critical designs.** Pays area
  cost for protection you don't need.

## Validation

```tcl
# Xilinx — check what encoding was picked
report_property [get_cells state_q_reg[*]]

# Look for FSM-related synthesis messages
report_methodology -severity {CRITICAL WARNING}

# Quartus
report_panel_full
# Inspect "Encoding Type" column in the State Machine Information table
```

After synthesis, every FSM in the design should appear in the
synthesis report with:

- Detected state count.
- Encoding (one_hot, binary, gray, etc.).
- Reachable state count.
- Any unreachable / safe-state additions.

If a coded FSM doesn't appear in the report, it wasn't recognized —
restructure to canonical form.

## Citations

- **Kilts**, *Advanced FPGA Design*, Wiley 2007, Chapter 14.4 — FSM
  compilation, encoding trade-offs.
- **Xilinx UG901** — Vivado FSM extraction and encoding directives.
- **Cliff Cummings**, *"State Machine Coding Styles for Synthesis,"*
  SNUG 2000.

## See also

- `fsm-design` skill — FSM coding patterns, one/two/three-process
  forms, timeout counters.
- `rtl-coding-for-synthesis.md` — canonical patterns that ensure
  recognition.
- `synthesis-attributes.md` — `FSM_ENCODING`, `SAFE_STATE`,
  `KEEP_FSM_ENCODING`.
- `clock-domain-crossing` skill — gray-encoded state crossing into
  another domain.
