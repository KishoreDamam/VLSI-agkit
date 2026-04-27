---
name: "fsm-design"
description: "FSM coding style, state encoding, latch avoidance, timeout patterns, and code-review checklist for RTL state machines"
type: coding
---

# FSM Design

> Three-process SystemVerilog FSMs that synthesize clean on any target — no latches, no illegal states, no missed handshakes.

## When to use

- Writing a new control FSM (memory controller, protocol adapter, arbiter, sequencer)
- Debugging synthesis warnings about inferred latches in a combinational always block
- Choosing state encoding (one-hot vs binary vs gray) for a specific target or path
- Code-reviewing an FSM written by someone else
- Adding a programmable timeout to an existing FSM without bloating it

## Quick reference

| Pattern | Use when | Anti-pattern |
|---|---|---|
| Three-process (seq reg + comb NS + comb out) | Default for all RTL FSMs | Single-process mixing seq/comb logic |
| Two-process (seq + comb NS+out combined) | Tiny FSMs (≤3 states, few outputs) | Single `always_ff` computing next state |
| One-hot encoding | FPGA critical path, Ultrascale+, ≤32 states | Binary on FPGA when timing is the constraint |
| Binary encoding | ASIC, area-limited designs, >32 states | One-hot in ASIC when FF count matters |
| Separate timeout counter | Programmable wait (100 ns–10 µs range) | Adding wait-states inside the FSM itself |
| Default assignment before `case` | Guarantee all outputs assigned (no latches) | Relying on `unique case` alone |

## Core patterns

### Pattern 1 — Three-process FSM (canonical)

- **Use when:** any production FSM; cleanest separation for lint, review, and code coverage
- **Code:**

  ```systemverilog
  typedef enum logic [2:0] { IDLE, REQ, ACTIVE, DRAIN, DONE, ERR } state_t;
  state_t state, next_state;

  // Process 1: state register
  always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n) state <= IDLE;
      else        state <= next_state;
  end

  // Process 2: next-state logic (default-before-case, covers all states)
  always_comb begin
      next_state = state;
      case (state)
          IDLE:   if (start)       next_state = REQ;
          REQ:    if (grant)       next_state = ACTIVE;
          ACTIVE: if (done)        next_state = DRAIN;
                  else if (err_in) next_state = ERR;
          DRAIN:                   next_state = DONE;
          default:                 next_state = IDLE;
      endcase
  end
  // Process 3: output logic — see references/encoding-tradeoffs.md §Three-process
  ```

- **Gotchas:**
  - Forgetting `default` assignments before `case` → latch inference on every output not touched in every branch.
  - Using `always @*` instead of `always_comb` — SystemVerilog `always_comb` adds an implicit sensitivity check at time zero; `always @*` does not.
  - Mixing `next_state` and `state` assignments inside the same comb block — synthesis treats them identically but lint flags the intent.

> Full tradeoff table for two-process vs three-process is in `references/encoding-tradeoffs.md`.

### Pattern 2 — Latch avoidance (fixing incomplete case)

- **Use when:** synthesis reports "latch inferred for signal X" or "incomplete case"
- **Code:**

  ```systemverilog
  // BAD — latch on 'out' when state != DATA
  always_comb begin
      case (state)
          DATA: out = payload;   // 'out' unassigned in IDLE, STOP → latch
      endcase
  end

  // GOOD — default assignment eliminates all latches
  always_comb begin
      out = '0;                  // default covers every branch
      case (state)
          DATA: out = payload;
      endcase
  end

  // ALSO GOOD — full branch assignment (verbose but explicit)
  always_comb begin
      case (state)
          IDLE: out = '0;
          DATA: out = payload;
          STOP: out = '0;
          default: out = '0;
      endcase
  end
  ```

- **Gotchas:**
  - `unique case` on `next_state` with full branch coverage does eliminate the state latch, but it does NOT help output signals that are missing assignments in some branches — those still infer latches. Add `default` output assignments before the `case` regardless.
  - Registered outputs (`always_ff` computing next-cycle value from `next_state`) eliminate the latch concern entirely but add one cycle of latency.

### Pattern 3 — Timeout counter (separate from FSM)

- **Use when:** FSM needs a programmable wait of N clock cycles without adding wait-states to the FSM graph
- **Code:**

  ```systemverilog
  // Separate programmable counter — FSM loads it; reads expired flag
  logic [15:0] tmr_cnt;
  logic        tmr_load, tmr_expired;
  logic [15:0] timeout_val;   // from register map / parameter

  always_ff @(posedge clk or negedge rst_n) begin
      if      (!rst_n)   tmr_cnt <= '0;
      else if (tmr_load) tmr_cnt <= timeout_val;
      else if (tmr_cnt != '0) tmr_cnt <= tmr_cnt - 1;
  end
  assign tmr_expired = (tmr_cnt == '0);

  // FSM uses tmr_load (output) and tmr_expired (input)
  // In next-state block:
  //   WAIT: if (tmr_expired) next_state = DONE;
  // In output block:
  //   ISSUE: tmr_load = 1'b1;   // pulses for one cycle
  ```

- **Gotchas:**
  - `tmr_load` must be a one-cycle pulse, not a level signal, or the counter never decrements.
  - Counting to zero means `timeout_val = 0` → instant expire; add a guard if zero is a legal register value.
  - For 100 ns–10 µs at 100 MHz: `timeout_val` range is 10–1000 (10 bits sufficient).

> Full counter + FSM code with programmable timeout in `references/timeout-counters.md`.

### Pattern 4 — One-hot encoding on FPGA

- **Use when:** FSM is on a critical path, targeting FPGA (especially Ultrascale+), ≤32 states
- **Code:**

  ```systemverilog
  typedef enum logic [6:0] {
      IDLE        = 7'b000_0001,
      ARB         = 7'b000_0010,
      READ_ISSUE  = 7'b000_0100,
      READ_DATA   = 7'b000_1000,
      WRITE_ISSUE = 7'b001_0000,
      WRITE_RESP  = 7'b010_0000,
      ERROR       = 7'b100_0000
  } state_t;

  // Transition decodes directly from a single FF bit — no LUT decode
  always_comb begin
      next_state = IDLE;
      unique case (1'b1)
          state[0]: if (start) next_state = ARB; else next_state = IDLE;
          state[1]: next_state = is_write ? WRITE_ISSUE : READ_ISSUE;
          // ...
          default:  next_state = IDLE;
      endcase
  end
  ```

- **Gotchas:**
  - `unique case (1'b1)` with one-hot state vector — ensures exactly one bit matches; synthesis verifies.
  - Vivado default auto-encoding is often one-hot for ≤32 states; explicit enum values override the tool. Use `(* fsm_encoding = "one_hot" *)` attribute if letting the tool choose.
  - State bit used as mux select avoids a decoder stage — this is the primary timing benefit over binary.

> Full one-hot vs binary vs gray tradeoff with FPGA and ASIC guidance in `references/encoding-tradeoffs.md`.

## Anti-patterns (do NOT do this)

1. **Single `always_ff` for everything** — mixing next-state computation and output registration in one clocked block prevents lint tools from detecting latch inference, and adds a pipeline cycle to every output whether you want it or not.

2. **No reset on state register** — after power-up, state FFs hold an unknown value. Simulation shows `X` propagation; silicon starts in an arbitrary state. Every FSM must have a deterministic reset path.

3. **Driving handshake signals (ready/valid) from a different always block than the FSM** — the signals get out of phase with state transitions. `awready`, `wready`, `bvalid` must be assigned in the FSM output block that observes the current state.

4. **Missing `default` case in next-state** — if synthesis finds an unreachable state encoding (e.g., two-bit binary that should be 00–10 but never 11), the `default` forces the machine out of any corrupted state. Without it the tool may infer a latch or leave recovery undefined.

5. **Encoding constants defined by hand for > 8 states with no typedef** — manually maintaining one-hot bit positions across 16+ states causes silent bugs when a state is added. Always use a `typedef enum` and let the tool or a parameterized macro compute the encoding.

6. **Using `state` (current) instead of `next_state` to drive registered outputs** — registered output from `state` adds two cycles of latency from input to registered output. If you want one-cycle-latency registered outputs, drive them from `next_state` in an `always_ff` block.

## Validation checklist (before declaring code "done")

- [ ] `always_comb` output block has default assignments before `case` — check every signal
- [ ] Every state in the enum appears in next-state `case`; `default` case exists
- [ ] State register has a synchronous or asynchronous reset to a known state
- [ ] All handshake outputs (ready, valid, ack) are driven by the FSM, not by separate logic
- [ ] Lint passes with zero "latch inferred" warnings (`Xcelium: %W,LATCHNO`, `DC: Warning: Latch inferred`)
- [ ] Formal or simulation reaches every state (state coverage = 100 %)
- [ ] ERROR or safe-landing `default` state exists and is reachable
- [ ] Timeout counter is separate from FSM state graph if wait duration is programmable
- [ ] One-hot: each state constant has exactly one bit set; enum values sum correctly
- [ ] SVA `state inside {…}` assertion covers all legal values

## Citations

- IEEE 1800-2017 §10.4.2 — non-blocking vs blocking assignments in `always_ff`; blocking in clocked blocks causes race conditions.
- IEEE 1800-2017 §12.5.3 — `always_comb` implicit sensitivity list and time-0 evaluation.

## See also

- `references/encoding-tradeoffs.md` — one-hot vs binary vs gray; FPGA vs ASIC; Vivado auto-encoding behaviour
- `references/timeout-counters.md` — separate counter pattern with programmable timeout; 100 ns–10 µs example
- `references/code-review-checklist.md` — full smell-list for FSM review: reset bugs, handshake bugs, style bugs
- `references/assertions.md` — SVA patterns for FSM: legal-state, liveness, no-deadlock, handshake invariants
- `examples/memctl_fsm.sv` — seven-state memory controller FSM (three-process, one-hot, ERROR state)
- `examples/tb_memctl_fsm.sv` — self-checking testbench (read path, write path, error injection)
