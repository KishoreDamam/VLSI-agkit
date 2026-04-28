# Timing Optimization Techniques

> Techniques for fixing timing violations (WNS < 0) after synthesis: pipelining, operand pre-registration, retiming, adder tree restructuring, and DSP cascading.

---

## Pipelining

### When to add register stages

Add a pipeline register when a combinational path between two registers exceeds the clock period. The rule of thumb:

- If `T_comb > T_clk − T_setup − T_skew`, insert a register to split the path.

### Latency vs throughput trade-off

| Configuration | Latency (cycles) | Throughput (ops/cycle) | When to use |
|---|---|---|---|
| Single-cycle (no pipeline) | 1 | 1 (if T_comb fits) | Simple paths, loose timing |
| 2-stage pipeline | 2 | 1 | One long op (e.g., multiply + add) |
| N-stage pipeline | N | 1 | Deep logic chains; DSP chains |
| N-stage with stall logic | N + stall | < 1 (stalls) | Data-dependent operations |

### Example: 3.2 ns multiplier-adder split into 2 stages

Target clock: 200 MHz (5 ns period), T_setup = 0.3 ns → max combinational path = 4.7 ns.
A multiply (1.8 ns) followed by an add (1.4 ns) = 3.2 ns total — fits in one cycle at 200 MHz.
But at 300 MHz (3.33 ns period), 3.2 ns > 3.0 ns (3.33 − 0.3) → violation. Solution: pipeline.

```systemverilog
// BEFORE (single-cycle, violates 300 MHz):
// assign result = (a * b) + c;   // 3.2 ns — too slow

// AFTER (pipelined, fits 300 MHz):
logic signed [31:0] product_r;   // Stage 1 output register

// Stage 1: multiply only (1.8 ns path)
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) product_r <= '0;
    else        product_r <= $signed(a) * $signed(b);
end

// Stage 2: add only (1.4 ns path)
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) result <= '0;
    else        result  <= product_r + $signed(c);
end
```

Both stages now fit within a 2.0 ns budget at 300 MHz (after setup margin).

---

## Operand Pre-Registration

### Concept

If one input to a multiply or multi-cycle operation is a **stable configuration value** (e.g., a coefficient loaded once and held), that operand can be registered one cycle earlier — moved from the cycle before the operation to two cycles before. This gives the multiply a full clock cycle with both operands already settled at the register outputs.

### When to use

- One operand changes infrequently (coefficient register, gain setting, address base).
- The multiply is still the critical path even after pipelining.
- The input operand arrives through a long combinational path from another block.

### Code example

```systemverilog
// cfg_coeff arrives through a long decode path — it is a config register
// that holds its value for at least 2 cycles after any write.
logic signed [15:0] coeff_pre_r;   // pre-registered coefficient

// Pre-register: capture coeff one cycle earlier
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) coeff_pre_r <= '0;
    else        coeff_pre_r <= cfg_coeff;   // registered one cycle ahead
end

// Multiply: both operands are now register outputs — full cycle available
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) product <= '0;
    else        product  <= $signed(data_in) * $signed(coeff_pre_r);
end
```

**Trade-off:** The coefficient update now has 1 extra cycle of latency before it affects the output. Acceptable for static or slowly-changing configuration.

---

## Retiming

Retiming moves existing registers across combinational logic without changing the input/output (I/O) behavior of the circuit. The tool re-balances the pipeline stages to equalize path delays.

### Vivado retiming

```tcl
# Forward retiming on multiplier cells — tool may push registers forward
# through combinational logic to balance the path
set_property RETIMING_FORWARD 1 [get_cells u_mult*]

# Can also apply globally (use with caution — may affect debug visibility)
set_property RETIMING_FORWARD 1 [get_cells -hierarchical -filter {PRIMITIVE_TYPE =~ REGISTER.*}]
```

Enable retiming during `synth_design`:
```tcl
synth_design -top top -part xcu250-figd2104-2L-e -retiming
```

### DC retiming

```tcl
# Allow boundary optimization (required for retiming across hierarchy)
set_boundary_optimization true

# Forward retiming across all registers
optimize_registers -forward

# Or combined forward/backward
optimize_registers
```

### Limitations

- Retiming cannot cross hierarchical boundaries by default. Set `set_boundary_optimization true` (DC) or `keep_hierarchy = "no"` (Vivado) on the relevant module.
- Retiming may move registers past clock-enable logic — verify that enable semantics are preserved.
- Not all register types can be retimed (e.g., registers with asynchronous set/reset may be excluded by the tool).
- After retiming, register names in the netlist may change — update `set_dont_touch` constraints if any were applied to individual registers.

---

## Adder Tree Restructuring

Synthesis tools can balance a tree of additions if given freedom to reorder operands. Forcing a left-to-right evaluation order with explicit parentheses prevents this optimization.

```systemverilog
// BAD: forces sequential left-to-right evaluation
// Tool sees: ((a+b)+c)+d — cannot rebalance
assign sum = ((a + b) + c) + d;

// GOOD: flat sum — tool can build a balanced 2-level tree
assign sum = a + b + c + d;

// ALSO GOOD: explicit balanced grouping
assign sum = (a + b) + (c + d);   // two parallel adds, then one add
```

### Why it matters

A balanced 4-input adder tree has a depth of 2 adder delays. A left-to-right chain has a depth of 3 adder delays. At high frequencies, the difference is significant.

### Larger trees

For 8+ operands, suggest balanced groupings explicitly:

```systemverilog
// 8-input balanced tree (3 levels)
logic [W:0] s01, s23, s45, s67, s0123, s4567;
assign s01   = a + b;
assign s23   = c + d;
assign s45   = e + f;
assign s67   = g + h;
assign s0123 = s01 + s23;
assign s4567 = s45 + s67;
assign sum   = s0123 + s4567;
```

---

## DSP Cascading (Xilinx UltraScale)

The Xilinx DSP48E2 (UltraScale/UltraScale+) has a built-in **pre-adder**: it can compute `(A + D) * B` in a single DSP slice — using two of the three inputs plus the pre-adder, with no extra LUT.

### Exploit the pre-adder

```systemverilog
// Structure that maps to DSP48E2 pre-adder + multiply in one slice:
// result = (a + d) * b
(* use_dsp = "yes" *)
logic signed [47:0] result;
assign result = ($signed(a) + $signed(d)) * $signed(b);
```

If instead written as `result = a*b + d*b`, the tool uses two DSP slices (one per multiply).

### DSP cascade for accumulate

```systemverilog
// Multiply-accumulate — maps to single DSP48E2 with P feedback
(* use_dsp = "yes" *)
logic signed [47:0] accum;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)     accum <= '0;
    else if (clr)   accum <= '0;
    else            accum <= accum + $signed(a) * $signed(b);
end
```

The DSP48E2 P-cascade path keeps the accumulator feedback inside the DSP at full speed, avoiding routing delay.

### Checking DSP inference

After synthesis, verify in the utilization report:
```
+----------------------------+------+-------+------------+-----------+-------+
|          Site Type         | Used | Fixed | Prohibited | Available | Util% |
+----------------------------+------+-------+------------+-----------+-------+
| DSPs                       |    2 |     0 |          0 |      3008 |  0.07 |
```

If DSP count is 0 and you expected DSPs, add `(* use_dsp = "yes" *)` or check that operands are `$signed`.
