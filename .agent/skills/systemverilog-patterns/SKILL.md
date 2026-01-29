---
name: systemverilog-patterns
description: SystemVerilog best practices, interfaces, packages, and modern constructs.
---

# SystemVerilog Patterns

> Modern SystemVerilog (SV2017) coding patterns for VLSI design.

---

## Interfaces

### Defining Interfaces

```systemverilog
interface axi_stream_if #(
    parameter int DATA_WIDTH = 32
) (
    input logic clk,
    input logic rst_n
);
    logic [DATA_WIDTH-1:0] tdata;
    logic                  tvalid;
    logic                  tready;
    logic                  tlast;
    
    modport master (
        output tdata, tvalid, tlast,
        input  tready
    );
    
    modport slave (
        input  tdata, tvalid, tlast,
        output tready
    );
endinterface
```

### Using Interfaces

```systemverilog
module producer (
    input  logic              clk,
    input  logic              rst_n,
    axi_stream_if.master      m_axis
);
    // Use m_axis.tdata, m_axis.tvalid, etc.
endmodule
```

---

## Packages

```systemverilog
package my_pkg;
    // Parameters
    parameter int DATA_WIDTH = 32;
    
    // Types
    typedef enum logic [1:0] {
        CMD_READ  = 2'b00,
        CMD_WRITE = 2'b01,
        CMD_RMW   = 2'b10
    } cmd_t;
    
    typedef struct packed {
        logic [15:0] addr;
        logic [15:0] data;
        cmd_t        cmd;
    } request_t;
    
    // Functions
    function automatic logic [7:0] crc8(input logic [63:0] data);
        // CRC calculation
    endfunction
endpackage
```

---

## Structs and Unions

### Packed Struct

```systemverilog
typedef struct packed {
    logic [3:0]  tag;
    logic [11:0] addr;
    logic [15:0] data;
} packet_t;  // Total: 32 bits, synthesizable
```

### Unpacked Struct

```systemverilog
typedef struct {
    int          count;
    string       name;
    logic [31:0] data;
} debug_info_t;  // For verification only
```

---

## Assertions

### Immediate Assertions

```systemverilog
always_comb begin
    assert (count <= MAX_COUNT)
        else $error("Count overflow");
end
```

### Concurrent Assertions

```systemverilog
// Property: valid followed by ready within 10 cycles
property p_handshake;
    @(posedge clk) disable iff (!rst_n)
    valid |-> ##[1:10] ready;
endproperty

assert property (p_handshake)
    else $error("Handshake timeout");

cover property (p_handshake);
```

### Common Sequences

```systemverilog
// Request followed by grant
sequence s_req_grant;
    req ##[1:5] grant;
endsequence

// Burst of N transfers
sequence s_burst(n);
    valid [*n];
endsequence
```

---

## Generate Constructs

### For Generate

```systemverilog
genvar i;
generate
    for (i = 0; i < N; i++) begin : gen_stage
        pipeline_stage u_stage (
            .clk   (clk),
            .in    (stage_data[i]),
            .out   (stage_data[i+1])
        );
    end
endgenerate
```

### If Generate

```systemverilog
generate
    if (USE_BRAM) begin : gen_bram
        bram_memory u_mem (...);
    end else begin : gen_lutram
        lutram_memory u_mem (...);
    end
endgenerate
```

---

## Functions and Tasks

### Functions (Combinational)

```systemverilog
function automatic logic [7:0] gray2bin(
    input logic [7:0] gray
);
    logic [7:0] bin;
    bin[7] = gray[7];
    for (int i = 6; i >= 0; i--)
        bin[i] = bin[i+1] ^ gray[i];
    return bin;
endfunction
```

### Tasks (Procedural)

```systemverilog
task automatic wait_cycles(input int n);
    repeat (n) @(posedge clk);
endtask
```

---

## Parameterization

### Type Parameters

```systemverilog
module fifo #(
    parameter type DATA_T = logic [31:0],
    parameter int  DEPTH  = 16
) (
    input  DATA_T i_data,
    output DATA_T o_data
);
endmodule

// Usage
fifo #(.DATA_T(my_struct_t), .DEPTH(32)) u_fifo (...);
```

---

## Useful Constructs

| Construct | Use |
|-----------|-----|
| `unique case` | No overlap, tool checks |
| `priority case` | Intentional priority |
| `$clog2(N)` | Log2 ceiling |
| `$bits(T)` | Bit width of type |
| `$size(A)` | Array size |
| `'0`, `'1`, `'x` | Fill patterns |

---

## Best Practices

- Use `logic` instead of `reg`/`wire`
- Use `always_ff`, `always_comb`, `always_latch`
- Use interfaces for complex buses
- Use packages for shared types
- Use assertions throughout
