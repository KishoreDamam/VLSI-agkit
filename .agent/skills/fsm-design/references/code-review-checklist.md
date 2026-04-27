# FSM Code Review Checklist

> Smell-list for reviewing FSM RTL. Work through sections in order — structural bugs first, then functional, then style.

---

## Section 1 — Reset and power-up safety

| # | Check | Pass condition | Fail example |
|---|---|---|---|
| R1 | State register has a reset | `always_ff @(posedge clk or negedge rst_n)` with `if (!rst_n) state <= IDLE` | `always_ff @(posedge clk)` with no reset arm |
| R2 | Reset drives a known, named state (not `'0` or `'x`) | `state <= IDLE` not `state <= 3'b000` (if IDLE happens to be 3'b000, still name it) | `state <= '0` |
| R3 | Async vs sync reset matches project convention | Consistent across all FFs in the design (check project DRC rule) | Mixed async/sync reset on adjacent FFs sharing a reset tree |
| R4 | Reset release is glitch-free | Reset comes from a synchronised source; not raw button or async GPIO | `rst_n` connected directly to a board GPIO without synchroniser |

---

## Section 2 — Latch inference

| # | Check | Pass condition | Fail example |
|---|---|---|---|
| L1 | Every output signal has a default assignment before `case` | `out = '0;` before `case (state)` | Signal assigned only in two of four state branches |
| L2 | `always_comb` used (not `always @*`) | `always_comb` detects missing sensitivity at time-0 | `always @(state)` — partial sensitivity list |
| L3 | `default` branch in every `case` | `default: next_state = IDLE;` | No `default` in a `casez` or binary `case` |
| L4 | Synthesis lint report shows zero "latch inferred" warnings | Clean run through `read_compile_ultra` or equivalent | `WARNING: Latch inferred for 'out'` |

---

## Section 3 — Handshake correctness

| # | Check | Pass condition | Fail example |
|---|---|---|---|
| H1 | Handshake outputs (ready, valid, ack) driven from FSM output block | Same `always_comb` that reads `state` | `awready` driven from a separate `assign` that checks a different signal |
| H2 | AXI VALID must not depend on READY — *IEEE IHI 0022 §A3.3.1* | `bvalid` asserted when FSM enters RESP state; not gated by `bready` | `assign bvalid = bready & (state == RESP)` |
| H3 | AXI VALID held until READY | `bvalid` stays asserted until `bready` is seen | `bvalid` deasserted after one cycle unconditionally |
| H4 | VALID/READY handshake checked for all AXI channels present | `aw`, `w`, `b`, `ar`, `r` channels each reviewed | Only `aw` channel reviewed |
| H5 | Outputs driven in every reachable state (no "only in WRITE but not IDLE") | Default `= '0` plus explicit in active states | `wready` not assigned in IDLE → latch or incorrect level |

---

## Section 4 — Coding style bugs

| # | Check | Pass condition | Fail example |
|---|---|---|---|
| S1 | Three-process style (or justified two-process) | Seq reg, comb NS, comb output in separate blocks | Single `always_ff` computing NS logic and driving outputs |
| S2 | `typedef enum` used for state type | Readable labels in waveforms and lint | `logic [2:0] state` with localparams for values |
| S3 | No blocking assignments in `always_ff` | All `always_ff` assignments use `<=` | `state = next_state` inside `always_ff` |
| S4 | No non-blocking assignments in `always_comb` | All `always_comb` assignments use `=` | `next_state <= state` inside `always_comb` |
| S5 | `next_state` initialised to `state` (hold) before `case` | Prevents NS falling through to X in simulation | `next_state` left uninitialised; first branch assigns it |

---

## Section 5 — Functional completeness

| # | Check | Pass condition | Fail example |
|---|---|---|---|
| F1 | Every state in the enum is reachable from reset | Simulation or formal reaches all states | `ERROR` state exists but no transition leads to it |
| F2 | Every state has an exit path (no deadlock) | No state is a terminal sink unless that is intended | `WAIT` state with no transition out if signal never arrives |
| F3 | Error/recovery state exists | `ERROR` or `default` lands in a safe state | No handling for illegal combinations |
| F4 | ERROR state behaviour is documented | Comment explains escape: "held until reset" or "auto-clear after N cycles" | `ERROR` state with silent return to IDLE without logging |
| F5 | Timeout guard for wait states | Any state that waits for an external signal has a timeout or watchdog | `WAIT_DATA: if (data_valid) next_state = DONE;` with no timeout |

---

## Section 6 — Example: AXI-Lite write FSM full review

Input for review (from eval prompt 4):

```systemverilog
always_ff @(posedge clk) begin
  case (state)
    IDLE:  if (awvalid) state <= WRITE;
    WRITE: if (wvalid)  state <= RESP;
    RESP:  if (bready)  state <= IDLE;
  endcase
end
```

Findings against this checklist:

| ID | Finding | Fix |
|---|---|---|
| R1 | No reset — state is undefined after power-up | Add `if (!rst_n) state <= IDLE;` |
| L3 | No `default` case — illegal state encodings have no recovery | Add `default: state <= IDLE;` |
| S1 | Single `always_ff` mixing NS and output — `awready`, `wready`, `bvalid` are absent | Move to three-process; add output block |
| H2 | `bvalid` not driven from FSM — RESP channel broken | Add `bvalid = (state == RESP)` in output block |
| H1 | `awready`, `wready` not driven anywhere | Drive from FSM output block |
| L1 | No default assignments — any added outputs will infer latches | Add default section to output block |
| F5 | No timeout on WRITE or RESP — deadlock if wvalid or bready never arrives | Add timeout counter or watchdog |
