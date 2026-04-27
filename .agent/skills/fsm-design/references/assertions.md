# SVA Patterns for FSM Verification

> SystemVerilog Assertion (SVA) patterns for state machines: legal-state coverage, liveness, handshake invariants, no-deadlock.

---

## When to add SVA to an FSM

- Simulation-only environments: `assert property` runs during simulation and catches bugs early.
- Formal verification: the same SVA properties become proof obligations for bounded/unbounded model checking.
- Gate-level simulation: assertions catch X-propagation and reset-escape bugs that RTL simulation misses.

---

## Pattern 1 — Legal state assertion

Catches simulations where the state register holds a value not in the enum (e.g., after reset escapes or memory corruption in emulation).

```systemverilog
// Immediate assertion — checked every cycle
always @(posedge clk) begin
    assert (state inside {IDLE, ARB, READ_ISSUE, READ_DATA,
                          WRITE_ISSUE, WRITE_RESP, ERROR})
        else $error("Illegal FSM state: %0d at time %0t", state, $time);
end
```

For one-hot encoded FSMs, check that exactly one bit is set:

```systemverilog
always @(posedge clk) begin
    if (!rst_n) begin
        // skip during reset
    end else begin
        assert ($onehot(state))
            else $error("Non-one-hot FSM state: %b at time %0t", state, $time);
    end
end
```

---

## Pattern 2 — Liveness: FSM eventually leaves idle

Proves the FSM responds to a trigger and does not get stuck.

```systemverilog
property p_start_exits_idle;
    @(posedge clk) disable iff (!rst_n)
    (state == IDLE && start) |-> ##[1:20] (state != IDLE);
endproperty
assert property (p_start_exits_idle)
    else $error("FSM stuck in IDLE after start asserted");
```

Adjust the bound (`##[1:20]`) to the maximum expected latency from `start` to leaving IDLE.

---

## Pattern 3 — No-deadlock: FSM returns to IDLE within bounded cycles

```systemverilog
// Any transaction that starts (busy asserts) must complete within MAX_CYCLES
localparam MAX_CYCLES = 64;

property p_no_deadlock;
    @(posedge clk) disable iff (!rst_n)
    $rose(busy) |-> ##[1:MAX_CYCLES] (state == IDLE);
endproperty
assert property (p_no_deadlock)
    else $error("Deadlock: busy asserted but IDLE not reached within %0d cycles", MAX_CYCLES);
```

---

## Pattern 4 — AXI handshake invariant (VALID must not depend on READY)

```systemverilog
// bvalid must not be gated by bready (AXI protocol rule — ARM IHI 0022 §A3.3.1)
// Once bvalid asserts it must stay high until bready acknowledges
property p_bvalid_stable;
    @(posedge clk) disable iff (!rst_n)
    (bvalid && !bready) |=> bvalid;
endproperty
assert property (p_bvalid_stable)
    else $error("bvalid deasserted before bready acknowledged");
```

---

## Pattern 5 — ERROR state only entered on known bad conditions

```systemverilog
// ERROR must only be reached from READ_DATA on unexpected data_valid deassertion
property p_error_entry;
    @(posedge clk) disable iff (!rst_n)
    $rose(state == ERROR) |-> $past(state == READ_DATA && !data_valid);
endproperty
assert property (p_error_entry)
    else $error("ERROR state entered from unexpected path");
```

---

## Pattern 6 — Output mutual exclusion

```systemverilog
// issue_read and issue_write should never assert simultaneously
property p_issue_mutex;
    @(posedge clk) disable iff (!rst_n)
    not (issue_read && issue_write);
endproperty
assert property (p_issue_mutex)
    else $error("issue_read and issue_write asserted simultaneously");
```

---

## Pattern 7 — Reset escape: state must be IDLE after reset deasserts

```systemverilog
property p_reset_escape;
    @(posedge clk)
    $fell(rst_n) |=> ##[0:5] (state == IDLE);
endproperty
assert property (p_reset_escape)
    else $error("FSM did not reach IDLE within 5 cycles of reset deassertion");
```

---

## Packaging assertions for synthesis exclusion

Wrap assertions in a `// synthesis translate_off` guard or a `generate` block gated by a parameter:

```systemverilog
`ifndef SYNTHESIS
// All SVA properties here
`endif
```

Or use a parameter-gated generate:

```systemverilog
generate
    if (ENABLE_ASSERTIONS) begin : g_fsm_sva
        assert property (p_start_exits_idle);
        assert property (p_no_deadlock);
        assert property (p_bvalid_stable);
    end
endgenerate
```

---

## Formal verification notes

When running JasperGold, SymbiYosys, or OneSpin against these properties:

- Set `MAX_CYCLES` to the smallest value that covers the design's real worst-case latency — large bounds cause state-space explosion.
- Add `assume` constraints for inputs that the design never actually sees (e.g., `assume (start == 0) during reset`).
- `disable iff (!rst_n)` is recognised by most formal tools as a reset vacuity guard — use it on every property that should only hold outside of reset.
- For unbounded proofs (k-induction), ensure all properties include a `disable iff` clause; otherwise the tool will try to prove them from time zero (including through reset).
