# Gate-Level Simulation (GLS) Readiness

> Why GLS differs from RTL simulation, the common hazards that cause failures, and how to prepare your design for a clean GLS run.

---

## Why GLS Differs from RTL Simulation

Gate-level simulation (GLS) runs the synthesized netlist — a structural description using library cells — rather than the behavioral RTL. Key differences:

| Aspect | RTL simulation | Gate-level simulation |
|---|---|---|
| `initial` blocks | Executed at time 0 | **Not present** — synthesis removes them |
| X-propagation | Operator-masking (e.g., `X & 0 = 0`) | Pessimistic through every gate |
| Timing | No delay (functional only) | Optional: SDF annotation adds real gate delays |
| Reset coverage | X in unreset FFs may be masked | Every unreset FF holds X; propagates forward |
| Library cells | Behavioral models | Library-specific gate models |
| Simulation speed | Fast | 5–50× slower than RTL |

---

## `initial` Block Hazard

### What synthesis does with `initial` blocks

Synthesis tools (Vivado, DC, Genus) **silently discard all `initial` statements**. They have no hardware equivalent in FPGA fabric (flip-flops power up to an undefined state unless configured otherwise) or in standard-cell ASIC libraries.

| Construct | Survives synthesis? | GLS behavior |
|---|---|---|
| `initial q = 1'b0;` | No | FF starts at X in GLS |
| `initial state = IDLE;` | No | State register starts at X; may lock up FSM |
| `initial $display(...)` | No | No output; silently removed |
| `initial #10 clk = 0;` | No — sim-only clock gen | No effect |
| Reset in `always_ff` | Yes | FF initialized to reset value at reset |

### Fix: replace `initial` with reset

```systemverilog
// BAD — initial block initializes; GLS will have X after reset
initial begin
    counter = '0;
    state   = IDLE;
end

// GOOD — explicit reset covers both RTL and GLS
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        counter <= '0;
        state   <= IDLE;
    end else begin
        counter <= counter + 1;
        state   <= next_state;
    end
end
```

---

## X-Propagation Modes

### Pessimistic (standard gate model)

The standard model: any gate with an X input produces an X output (unless the other input forces a known result — e.g., AND with 0 → 0, OR with 1 → 1). This is **pessimistic** because it flags conditions that might not fail in silicon.

- Cadence GLS (ncsim/xrun): defaults to pessimistic.
- Synopsys VCS: defaults to pessimistic.
- Mentor Questa: pessimistic by default; can enable optimistic with plusargs.

### Optimistic (Z-state or X-optimistic mode)

Some tools offer an optimistic mode where X is treated as a randomly chosen 0 or 1 each evaluation. This may hide failures in RTL but can occasionally mask real silicon issues too.

**Recommendation:** Always debug with pessimistic X-propagation first. Optimistic mode is useful only to distinguish "X causes this output" from "any value causes this output."

### Resolving X-propagation failures

1. Identify which register holds X after reset — use waveform viewer; trace X back to its source.
2. Verify the register is connected to the reset net (check the netlist or `report_clock_interaction`).
3. If the register is intentionally unreset (e.g., a scratchpad), add an explicit reset or mark the path as a false-reset in the GLS testbench.

---

## Reset Coverage

Every register in the synthesized netlist must reach a known state when the reset sequence runs.

### Finding unreachable registers

**Vivado:**
```tcl
# After synthesis:
report_clock_interaction -file clock_interaction.rpt
# Look for registers with no reset path in the "Reset" column
```

**Formal tools:**
```tcl
# Jasper/VC Formal reset check
check_reset -from rst_n
```

**Manual netlist grep (last resort):**
```bash
# Find FDCE cells (Xilinx async reset FF) that have no CLR connection
grep -A5 "FDCE" netlist.v | grep -v "CLR"
```

### Registers that commonly miss reset

- Debug observation registers (added late in the flow)
- Pipeline bubble registers (added by retiming — tool may not add reset)
- Shift registers used in LFSR patterns where reset is only applied to the seed register
- Pipeline registers added by synthesis retiming (tool may use FDRE without a CLR pin)

### Post-reset verification sequence

In the GLS testbench, always:
1. Assert reset for at least 4 clock cycles (covers multi-stage synchronizers).
2. Deassert reset synchronously (on a rising clock edge) to avoid metastability.
3. Verify that the first output transaction after reset produces the expected value before applying any other stimulus.

---

## SDF Annotation

Standard Delay Format (SDF) files contain the actual gate delays extracted from the placed-and-routed design. Back-annotating SDF enables **timing-accurate GLS** — the most conservative form of gate-level simulation.

### Testbench annotation

```systemverilog
module tb;
    // ...
    initial begin
        // Annotate after design is instantiated
        $sdf_annotate("design_routed.sdf", tb.dut);
    end

    top_module dut (
        .clk    (clk),
        .rst_n  (rst_n),
        .data_in(data_in),
        .data_out(data_out)
    );
endmodule
```

### SDF annotation options

| Option | Effect |
|---|---|
| Default (no scaling) | Use timing numbers as-is (typically slow-corner) |
| `+sdf_precision+1ps` | Set simulation precision to 1 ps |
| `+neg_tchk` | Allow negative timing checks (tool-specific) |
| `-typdelay` / `-mindelay` / `-maxdelay` | Select delay corner from SDF |

### When to run SDF-annotated GLS

- After place-and-route (not just synthesis) — SDF from synthesis is approximate.
- For sign-off verification of critical interfaces.
- When a functional bug is suspected to be timing-related (setup/hold violations in silicon).

SDF-annotated GLS is slow (10–50× slower than RTL). Run it on representative test cases, not the full regression suite.

---

## GLS Testbench Checklist

- [ ] `$sdf_annotate` present if timing-accurate GLS is required
- [ ] Reset asserted for ≥4 clock cycles before first data stimulus
- [ ] Reset deassertion is synchronous (aligned to rising clock edge)
- [ ] No `initial` blocks that set design signals — all initialization via reset or explicit stimulus
- [ ] X-check assertions: `assert (data_out !== 'x)` after reset deassertion + N cycles
- [ ] Testbench does not use `initial` to initialize DUT internal signals (not possible in GLS — no hierarchical access to internal nets in locked netlist)
- [ ] Functional equivalence with RTL regression results verified before taping out
