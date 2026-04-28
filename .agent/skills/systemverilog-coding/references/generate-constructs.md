# Generate Constructs Reference — SystemVerilog

## Overview

`generate` blocks allow parameterized structural replication and conditional inclusion
of hardware. They are elaborated at compile time; no runtime overhead.

---

## generate-for: replicating hardware N times

```systemverilog
module pipeline #(
    parameter int STAGES = 4,
    parameter int WIDTH  = 32
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [WIDTH-1:0] data_in,
    output logic [WIDTH-1:0] data_out
);
    // Parameter validation — fails loudly at elaboration
    initial begin
        assert (STAGES >= 1)
            else $fatal(1, "pipeline: STAGES must be >= 1");
    end

    logic [WIDTH-1:0] stage [0:STAGES];   // STAGES+1 nodes: 0..STAGES

    assign stage[0] = data_in;
    assign data_out = stage[STAGES];

    genvar i;
    generate
        for (i = 0; i < STAGES; i++) begin : gen_pipe
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n)
                    stage[i+1] <= '0;
                else
                    stage[i+1] <= stage[i];
            end
        end
    endgenerate
endmodule
```

Key points:
- `genvar` must be declared outside the `generate` block in most tools.
- The generate block label (`gen_pipe`) is required for hierarchical references.
- Array `stage[0:STAGES]` has STAGES+1 elements; stage[0] is the input wire,
  stage[STAGES] is the output wire.

---

## Edge cases in pipelined generate-for

| Edge case | Behavior |
|---|---|
| `STAGES = 1` | Single register; `stage[0]` = input, `stage[1]` = output. |
| `STAGES = 0` | Fails parameter assertion. Do not allow; direct connection would make the "pipeline" transparent. |
| `WIDTH = 1` | Works; `stage` becomes an array of 1-bit registers. |
| Large STAGES | Elaboration is static; no simulation overhead per stage. |

Stage indexing:
- `i = 0`: `stage[1] <= stage[0]` — first register, input from `data_in`.
- `i = STAGES-1`: `stage[STAGES] <= stage[STAGES-1]` — last register, output to `data_out`.

---

## generate-if: conditional hardware

```systemverilog
generate
    if (USE_BRAM) begin : gen_bram
        bram_512x32 u_mem (
            .clk(clk), .addr(addr), .din(wdata), .dout(rdata), .we(we)
        );
    end else begin : gen_distributed
        logic [31:0] mem [0:511];
        always_ff @(posedge clk)
            if (we) mem[addr] <= wdata;
        assign rdata = mem[addr];
    end
endgenerate
```

Gotchas:
- `generate-if` conditions must be constant expressions (no runtime variables).
- Both branches must be valid SystemVerilog even if only one is elaborated.
- Label both branches (`gen_bram`, `gen_distributed`) for hierarchical path clarity.

---

## Parameter validation patterns

### $fatal at elaboration time

```systemverilog
initial begin
    assert (DEPTH >= 2 && (DEPTH & (DEPTH-1)) == 0)
        else $fatal(1, "FIFO: DEPTH=%0d must be a power-of-2 >= 2", DEPTH);
end
```

`$fatal(1, ...)` terminates elaboration immediately with a non-zero exit code and
the message. `1` is the verbosity level.

### Conditional generate with $fatal

```systemverilog
generate
    if (STAGES < 1) begin
        $fatal(1, "STAGES must be >= 1");
    end
endgenerate
```

Note: `initial assert` is preferred over generate-if for parameter checks because
it provides better message formatting and is more universally supported.

### `localparam` derived from parameters

Derive secondary parameters with `localparam` to avoid repeating expressions and
to document intent:

```systemverilog
localparam int ADDR_BITS = $clog2(DEPTH);
localparam int TOTAL_W   = STAGES * WIDTH;
```

---

## Hierarchical references to generated instances

Generated instances are accessible via their label and index:

```systemverilog
// stage[] is declared at module scope — access it directly:
pipeline_inst.stage[2]    // output of stage 2 register

// gen_pipe[i] is the scope label for the always_ff instance:
// use it to reference named signals INSIDE the generate block, if any.
// pipeline_inst.gen_pipe[2].some_local_signal
```

This is useful in:
- SVA properties targeting specific pipeline stages.
- Waveform viewers to inspect individual stages.
- Formal tool cover points.

---

## Nested generate

Generate blocks can be nested, but this quickly becomes hard to read. Prefer
parameterized sub-modules over deep nesting.

```systemverilog
generate
    for (genvar r = 0; r < ROWS; r++) begin : gen_row
        for (genvar c = 0; c < COLS; c++) begin : gen_col
            pe_cell u_cell (.row(r), .col(c), ...);
        end
    end
endgenerate
```

---

## Common generate gotchas

| Gotcha | Detail |
|---|---|
| `genvar` in multiple generate blocks | A `genvar` declared once can be reused in multiple separate `generate-for` loops in the same module. |
| Signals declared inside `generate` | Signals declared inside a labeled generate block have their own scope. They are not visible outside without the hierarchical path. |
| `generate-for` index is not a logic signal | `genvar` values are elaboration-time constants; you cannot use them in runtime expressions outside the generate block. |
| Tool elaboration order | Some tools require `genvar` declarations before the `generate` keyword; others allow inline `for (genvar i = ...)`. Declare outside for maximum portability. |
| Named-generate and port connections | When instantiating inside a generate block, use named port connections (`.port(signal)`) for clarity. |
