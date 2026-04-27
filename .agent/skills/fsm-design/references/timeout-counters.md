# FSM Timeout Counters

> Separate counter pattern for programmable FSM timeouts — keeps the state graph clean and the timeout configurable at runtime.

---

## Why a separate counter, not FSM wait-states

Adding wait-states directly to an FSM (`WAIT_1`, `WAIT_2`, … `WAIT_N`) creates N new states, explodes the state diagram, and makes the timeout hard to change without modifying RTL. A separate counter decouples the timing from the state graph:

- The FSM stays simple — one WAIT state instead of N.
- The timeout duration is a data value (counter load), not a structural property.
- The counter can be reused by multiple FSMs or re-loaded mid-operation.

---

## Basic pattern

```systemverilog
// Separate programmable timeout counter
// - FSM asserts tmr_load for one cycle to start the timer
// - FSM reads tmr_expired to know when to proceed

parameter int CLK_FREQ_HZ = 100_000_000;  // 100 MHz

// Timeout range: 100 ns–10 µs @ 100 MHz = 10–1000 cycles → 10-bit counter
localparam int TMR_W = 10;

logic [TMR_W-1:0] tmr_cnt;
logic             tmr_load, tmr_expired;
logic [TMR_W-1:0] timeout_val;  // loaded from register or parameter

always_ff @(posedge clk or negedge rst_n) begin
    if      (!rst_n)           tmr_cnt <= '0;
    else if (tmr_load)         tmr_cnt <= timeout_val;
    else if (tmr_cnt != '0)    tmr_cnt <= tmr_cnt - 1;
end

assign tmr_expired = (tmr_cnt == '0) && !tmr_load;
```

**FSM usage (output block):**

```systemverilog
// Output defaults
tmr_load = 1'b0;

case (state)
    ISSUE:  tmr_load = 1'b1;   // one-cycle pulse loads counter
    WAIT:   ;                   // do nothing; wait for expired
    default: ;
endcase
```

**FSM usage (next-state block):**

```systemverilog
case (state)
    ISSUE:  next_state = WAIT;
    WAIT:   if (tmr_expired) next_state = DONE;
            else             next_state = WAIT;
    default: next_state = IDLE;
endcase
```

---

## Calculating timeout_val

| Timeout | Clock | Cycles | Bits needed |
|---|---|---|---|
| 100 ns | 100 MHz | 10 | 4 |
| 1 µs | 100 MHz | 100 | 7 |
| 10 µs | 100 MHz | 1000 | 10 |
| 100 µs | 100 MHz | 10 000 | 14 |
| 1 ms | 100 MHz | 100 000 | 17 |

**Formula:** `timeout_val = ceil(timeout_ns * clk_freq_hz / 1e9) - 1`

The `-1` accounts for the fact that a counter loaded with value N counts N+1 cycles before reaching 0 if the load cycle counts as cycle 1. To be explicit, define the convention in a comment and test it in the testbench.

---

## Shared counter for multiple FSM states

If more than one FSM state needs a timeout, share the same counter with a one-hot enable:

```systemverilog
typedef enum logic [1:0] {TMRSRC_IDLE, TMRSRC_ARB, TMRSRC_WAIT} tmrsrc_t;
tmrsrc_t tmr_src;

logic [15:0] timeout_arb  = 16'd50;    // 500 ns @ 100 MHz
logic [15:0] timeout_wait = 16'd1000;  // 10 µs @ 100 MHz

// Mux timeout value by FSM context
always_comb begin
    case (tmr_src)
        TMRSRC_ARB:  timeout_val = timeout_arb;
        TMRSRC_WAIT: timeout_val = timeout_wait;
        default:     timeout_val = '0;
    endcase
end
```

---

## Edge cases and gotchas

1. **`tmr_load` is a pulse, not a level.** If `tmr_load` stays asserted for two cycles, the counter resets on cycle 2 and the timeout never elapses. The FSM output block must ensure `tmr_load` is only high during the one cycle the FSM transitions into the WAIT state.

2. **`timeout_val = 0` → instant expire.** If 0 is a valid register value (meaning "no wait"), include a guard:

   ```systemverilog
   assign tmr_expired = (tmr_cnt == '0) && (timeout_val != '0 || tmr_load);
   // Or: treat 0 as "skip timeout"
   ```

3. **Counter width.** Size it for the maximum timeout, not the typical case. Use `$clog2(max_cycles + 1)` for a parameterised width.

4. **tmr_expired glitch on load.** When `tmr_load` is asserted and `tmr_cnt` is currently 0, `tmr_expired` would be true on the same cycle as the load. The guard `!tmr_load` in the `assign` above prevents the FSM from seeing a spurious expire at load time.

5. **Resettable counters in formal.** Formal tools need a bounded proof depth greater than `timeout_val` to fully verify the timer path. Consider parameterising `timeout_val` to a small value in formal builds.

---

## Full worked example — ARB timeout in memctl FSM

The `examples/memctl_fsm.sv` file does not include a timeout (the spec does not require one), but here is a drop-in snippet extending it with an arbitration timeout:

```systemverilog
// Added signals
logic        tmr_load, tmr_expired;
logic [9:0]  tmr_cnt;
localparam   ARB_TIMEOUT = 10'd999;  // 10 µs @ 100 MHz

// Counter
always_ff @(posedge clk or negedge rst_n) begin
    if      (!rst_n)        tmr_cnt <= '0;
    else if (tmr_load)      tmr_cnt <= ARB_TIMEOUT;
    else if (tmr_cnt != '0) tmr_cnt <= tmr_cnt - 1;
end
assign tmr_expired = (tmr_cnt == '0) && !tmr_load;

// In next-state block, ARB case becomes:
// ARB: if      (arb_sel && tmr_expired) next_state = ERROR;
//      else if (arb_sel)                next_state = is_write ? WRITE_ISSUE : READ_ISSUE;
//      else                             next_state = ARB;

// In output block:
// ARB: tmr_load = (state != ARB);   // load on entry only
//      busy     = 1'b1;
```
