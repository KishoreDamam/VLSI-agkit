# FSM State Encoding Tradeoffs

> One-hot vs binary vs gray — when each wins on FPGA and ASIC targets.

---

## Summary table

| Encoding | Bits for N states | Typical use | Primary benefit | Primary cost |
|---|---|---|---|---|
| Binary | ceil(log2 N) | ASIC, >32 states, area-limited | Minimum flip-flops | Decode LUT on every transition |
| One-hot | N | FPGA critical path, ≤32 states | No decode stage; single-FF select | N flip-flops per state |
| Gray | ceil(log2 N) | CDC state observation, low power | Single-bit change per transition | Complex next-state decode |
| Johnson | 2*ceil(log2 N) | Low-glitch output mux | Reduced glitch energy | More FFs than binary |

---

## One-hot on FPGA (recommended for critical paths)

### Why it wins timing

On LUT-based FPGAs (Xilinx Ultrascale+, Versal, Intel Agilex), the critical path through an FSM is typically:

```
FF output → next-state LUT → FF input
```

With **binary encoding** of an 8-state FSM (3 bits), every transition condition must include a 3-input decode (`state == 3'b101`), consuming LUT inputs that could otherwise be used for the actual transition condition.

With **one-hot encoding**, the current-state FF output *is* the select signal. A transition from `READ_DATA` checks `state[3]` — one LUT input consumed, not three. The remaining inputs are available for `data_valid`, `err_flag`, etc., potentially collapsing what would be two LUT levels into one.

### Register cost

For an 8-state FSM on a Xilinx Ultrascale+:
- Binary: 3 FFs
- One-hot: 8 FFs

On an FPGA with tens of thousands of slice registers available, the 5-FF overhead is negligible. The timing gain from removing a decode stage is not.

### Vivado auto-encoding behaviour

Vivado defaults to **one-hot** encoding for FSMs with ≤ ~32 states when synthesis attribute `fsm_encoding` is not set. For larger FSMs (>32 states), Vivado switches to binary. You can override:

```systemverilog
// Override to force one-hot regardless of size
(* fsm_encoding = "one_hot" *) state_t state;

// Other valid values: "binary", "gray", "johnson", "sequential", "auto"
// "auto" = Vivado default (one-hot for ≤32, binary above)
```

**Important:** if you declare explicit enum values (e.g., `IDLE = 7'b000_0001`), Vivado uses your encoding and ignores the attribute. If you omit explicit values, the attribute takes effect.

### Debugging with enums vs raw bits

Using `typedef enum` preserves readable state names in waveform viewers regardless of encoding:
- Vivado `xsim`, Questa, VCS all display the enum label (e.g., `READ_DATA`) rather than `3'b011`.
- With one-hot and explicit bit vectors *without* a typedef, waveforms show raw hex — harder to read.
- **Always use a typedef enum** even with one-hot explicit bit patterns.

---

## Binary on ASIC (default for area-limited targets)

### Why it wins area

ASIC standard-cell FFs have much higher area cost per bit than FPGA slice registers. For a 16-state FSM:
- Binary: 4 FFs
- One-hot: 16 FFs

At 28 nm, a D flip-flop costs roughly 8–12 gate equivalents. 12 extra FFs = ~100–144 GE overhead per FSM instance. If the design has dozens of FSMs, this adds up.

### Timing on ASIC

ASIC synthesis (DC, Genus) retimes and optimises the decode logic. The binary decode that costs extra LUT levels on an FPGA is usually absorbed into a single NAND/NOR tree in CMOS. The one-hot timing advantage largely disappears after synthesis optimisation.

**Caveat:** on a truly critical path (e.g., the FSM driving an address pipeline), the synthesis tool may not fully optimise the decode away. Profile with timing reports before assuming binary is fast enough.

---

## Gray encoding for CDC observation

Gray encoding is **not** primarily a performance encoding. Use it when:

1. The FSM state must be observed across a clock domain boundary (e.g., a status register sampled by a slower bus clock).
2. Only one bit changes per state transition — makes the value safe to sample asynchronously (at most one bit of metastability).

Gray code only works cleanly for one-way sequential state progressions (0→1→2→3→…). If your FSM has non-sequential transitions (IDLE can jump to any of five states), gray encoding provides no benefit and the single-bit-change property is lost.

---

## Choosing encoding: decision guide

```
Is the FSM on a timing-critical path?
  └─ Yes: FPGA? → one-hot (≤32 states)
          ASIC?  → binary first; try one-hot only if timing still fails after retiming
  └─ No: FPGA, area not critical → let Vivado auto-encode (default: one-hot ≤32)
         ASIC, area-limited     → binary
         State must cross CDC   → gray (only if sequential transitions)
         >32 states, FPGA       → binary (one-hot register count becomes prohibitive)
```

---

## Example: 8-state FSM, Xilinx Ultrascale+, binary vs one-hot

**Binary (3-bit):**

```systemverilog
typedef enum logic [2:0] {
    IDLE        = 3'd0,
    ARB         = 3'd1,
    READ_ISSUE  = 3'd2,
    READ_DATA   = 3'd3,
    WRITE_ISSUE = 3'd4,
    WRITE_RESP  = 3'd5,
    ERROR       = 3'd6
} state_t;
```

**One-hot (7-bit):**

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
```

With one-hot, the transition decode becomes:

```systemverilog
// Direct bit test — no multi-bit decoder needed
always_comb begin
    next_state = IDLE;
    unique case (1'b1)
        state[0]: if (start) next_state = ARB; else next_state = IDLE;     // IDLE
        state[1]: next_state = arb_sel ? WRITE_ISSUE : READ_ISSUE;         // ARB
        state[2]: next_state = READ_DATA;                                   // READ_ISSUE
        state[3]: if (data_valid) next_state = IDLE; else next_state = ERROR; // READ_DATA
        state[4]: next_state = WRITE_RESP;                                  // WRITE_ISSUE
        state[5]: if (resp_ready) next_state = IDLE; else next_state = WRITE_RESP; // WRITE_RESP
        state[6]: next_state = ERROR;                                       // ERROR — held until reset
        default:  next_state = IDLE;
    endcase
end
```

`unique case (1'b1)` tells the synthesiser exactly one bit will be set — it does not add a priority encoder or report a coverage gap.
