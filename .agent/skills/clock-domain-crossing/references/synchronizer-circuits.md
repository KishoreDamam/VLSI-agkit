# Synchronizer Circuits

Deep reference for 2-FF, 3-FF, reset, and pulse synchronizers.

---

## 2-FF Synchronizer (standard)

The canonical single-bit synchronizer. Metastability MTBF increases exponentially
with each additional stage; 2 stages is the industry baseline.

```systemverilog
module sync_2ff #(
    parameter int WIDTH  = 1,
    parameter int STAGES = 2
) (
    input  logic             clk_dst,
    input  logic             rst_n,
    input  logic [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q
);
    (* ASYNC_REG = "TRUE" *)
    logic [STAGES-1:0][WIDTH-1:0] pipe;

    always_ff @(posedge clk_dst or negedge rst_n) begin
        if (!rst_n)
            pipe <= '0;
        else begin
            pipe[0] <= d;
            for (int i = 1; i < STAGES; i++)
                pipe[i] <= pipe[i-1];
        end
    end

    assign q = pipe[STAGES-1];
endmodule
```

**ASYNC_REG attribute** tells Vivado (and other tools that honor it) to place
the chain of FFs in adjacent slices and prevent logic insertion between them.
Synopsys DC uses `set_dont_touch`; Cadence Genus uses `dont_touch` property —
set these on the synchronizer cells in synthesis scripts.

**Width > 1:** Only safe for Gray-coded multi-bit signals or one-hot encoded
signals where only one bit changes per clock. Never use WIDTH > 1 for arbitrary
binary buses.

---

## 3-FF Synchronizer (high-speed / safety-critical)

Use when the destination clock period is short enough that a 2-FF synchronizer's
MTBF falls below the target system lifetime, or when functional safety standards
(ISO 26262, IEC 61508) require a documented MTBF margin.

```systemverilog
// Instantiate sync_2ff with STAGES=3
sync_2ff #(.WIDTH(1), .STAGES(3)) u_sync (
    .clk_dst(clk_dst),
    .rst_n  (rst_n),
    .d      (async_in),
    .q      (sync_out)
);
```

**When to use 3 FF:**
- Destination clock > 500 MHz, or
- Required MTBF > 10^9 years at the application operating temperature, or
- Safety-critical application with documented metastability budget

---

## Reset Synchronizer

Async assert, synchronous deassert — one synchronizer instance per destination
clock domain.

```systemverilog
module reset_sync (
    input  logic clk_dst,
    input  logic async_rst_n,   // active-low async reset input
    output logic sync_rst_n     // active-low sync reset output
);
    (* ASYNC_REG = "TRUE" *)
    logic [1:0] rst_pipe;

    // Assert immediately (async), deassert synchronously
    always_ff @(posedge clk_dst or negedge async_rst_n) begin
        if (!async_rst_n)
            rst_pipe <= 2'b00;
        else
            rst_pipe <= {rst_pipe[0], 1'b1};
    end

    assign sync_rst_n = rst_pipe[1];
endmodule
```

**Instantiate once per clock domain.** Three domains → three `reset_sync` instances,
each driven by the same `async_rst_n` source.

**Spyglass waiver:** The CDC tool flags the asynchronous assertion path (D pin of
first FF). This is expected and correct behavior; the assert is intended to be
asynchronous. Add a waiver:

```tcl
# Spyglass waiver — async assert on reset synchronizer first-stage D pin is by design
waive -rule {CDC_RESET_SIGNAL} -comment "Async assert intended; sync deassert via reset_sync"
```

**SDC constraint:**

```tcl
# False path on the D input of the first synchronizer FF (async assert is not a timing path)
set_false_path -to [get_pins -hierarchical -filter {NAME =~ */rst_pipe[0]/D}]
```

---

## Pulse Synchronizer

Safe single-pulse transfer from slow or fast source to any destination, using a
toggle-detect scheme. Guarantees no pulses are lost (provided source pulse width
≥ 1 destination period) and no spurious pulses are generated.

```systemverilog
module pulse_sync (
    input  logic clk_src,
    input  logic clk_dst,
    input  logic rst_src_n,
    input  logic rst_dst_n,
    input  logic pulse_in,    // 1-cycle pulse in clk_src domain
    output logic pulse_out    // 1-cycle pulse in clk_dst domain
);
    logic toggle_src;
    logic toggle_dst_q, toggle_dst_d;

    // Toggle register in source domain
    always_ff @(posedge clk_src or negedge rst_src_n) begin
        if (!rst_src_n) toggle_src <= 1'b0;
        else if (pulse_in) toggle_src <= ~toggle_src;
    end

    // Synchronize toggle to destination
    sync_2ff #(.WIDTH(1), .STAGES(2)) u_sync (
        .clk_dst(clk_dst),
        .rst_n  (rst_dst_n),
        .d      (toggle_src),
        .q      (toggle_dst_q)
    );

    // Edge detect → pulse
    always_ff @(posedge clk_dst or negedge rst_dst_n) begin
        if (!rst_dst_n) toggle_dst_d <= 1'b0;
        else toggle_dst_d <= toggle_dst_q;
    end

    assign pulse_out = toggle_dst_q ^ toggle_dst_d;
endmodule
```

**Minimum source pulse width:** The source pulse must hold for at least 1 full
`clk_src` cycle. The toggle approach handles pulses narrower than the destination
period — but only one pulse can be in-flight at a time (source must not re-pulse
until the previous toggle is visible in the destination).

**Throughput:** Source must not re-pulse within `(STAGES + 1)` destination clock
periods of the previous pulse. For same-frequency domains this gives a maximum
rate of `f_dst / (STAGES + 1)`. For fast-source / slow-destination, express
the constraint in source cycles: `ceil((STAGES + 1) × T_dst / T_src)` source
cycles between pulses. Example: STAGES=2, 500 MHz src / 10 MHz dst →
`ceil(3 × 100 ns / 2 ns) = 150` source cycles between pulses.
