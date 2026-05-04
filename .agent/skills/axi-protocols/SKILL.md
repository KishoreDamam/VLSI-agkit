---
name: axi-protocols
description: Use when designing or verifying an AXI4, AXI4-Lite, or AXI4-Stream interface — handshake VALID/READY rules, burst types, channel dependency ordering, register-slave implementation, or stream processing.
---

# AXI Protocols

> ARM AMBA AXI bus protocol patterns.

---

## When to use

- Connecting an IP to an SoC fabric or microcontroller subsystem.
- Implementing a register/CSR slave (AXI4-Lite) or DMA master (AXI4 full).
- Building or verifying streaming interfaces (AXI4-Stream) between processing blocks.
- Debugging handshake hangs, channel-ordering deadlocks, or RRESP/BRESP errors.

**Not for:** AHB/APB (different protocol family); custom point-to-point handshakes (use plain `valid`/`ready` instead of full AXI overhead).

---

## Protocol Overview

| Protocol | Use Case |
|----------|----------|
| AXI4 | High-performance memory-mapped |
| AXI4-Lite | Simple register access |
| AXI4-Stream | Streaming data |

---

## AXI4-Lite (Registers)

### Interface

```systemverilog
interface axi_lite_if #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32
) (
    input logic aclk,
    input logic aresetn
);
    // Write Address
    logic [ADDR_WIDTH-1:0] awaddr;
    logic                  awvalid;
    logic                  awready;
    
    // Write Data
    logic [DATA_WIDTH-1:0]   wdata;
    logic [DATA_WIDTH/8-1:0] wstrb;
    logic                    wvalid;
    logic                    wready;
    
    // Write Response
    logic [1:0] bresp;
    logic       bvalid;
    logic       bready;
    
    // Read Address
    logic [ADDR_WIDTH-1:0] araddr;
    logic                  arvalid;
    logic                  arready;
    
    // Read Data
    logic [DATA_WIDTH-1:0] rdata;
    logic [1:0]            rresp;
    logic                  rvalid;
    logic                  rready;
endinterface
```

### Slave Implementation

```systemverilog
module axi_lite_slave #(
    parameter int ADDR_WIDTH = 12
) (
    input  logic aclk,
    input  logic aresetn,
    axi_lite_if.slave s_axi
);

    // Registers
    logic [31:0] reg_ctrl;
    logic [31:0] reg_status;
    
    // Write FSM
    typedef enum logic [1:0] {
        WR_IDLE, WR_DATA, WR_RESP
    } wr_state_t;
    wr_state_t wr_state;
    
    logic [ADDR_WIDTH-1:0] wr_addr;
    
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            wr_state <= WR_IDLE;
            s_axi.awready <= 1'b0;
            s_axi.wready  <= 1'b0;
            s_axi.bvalid  <= 1'b0;
        end else begin
            case (wr_state)
                WR_IDLE: begin
                    s_axi.awready <= 1'b1;
                    if (s_axi.awvalid && s_axi.awready) begin
                        wr_addr <= s_axi.awaddr;
                        s_axi.awready <= 1'b0;
                        s_axi.wready  <= 1'b1;
                        wr_state <= WR_DATA;
                    end
                end
                WR_DATA: begin
                    if (s_axi.wvalid && s_axi.wready) begin
                        // Write to register
                        case (wr_addr[11:0])
                            12'h000: reg_ctrl <= s_axi.wdata;
                        endcase
                        s_axi.wready <= 1'b0;
                        s_axi.bvalid <= 1'b1;
                        s_axi.bresp  <= 2'b00; // OKAY
                        wr_state <= WR_RESP;
                    end
                end
                WR_RESP: begin
                    if (s_axi.bready) begin
                        s_axi.bvalid <= 1'b0;
                        wr_state <= WR_IDLE;
                    end
                end
            endcase
        end
    end
    
endmodule
```

---

## AXI4-Stream

### Interface

```systemverilog
interface axis_if #(
    parameter int DATA_WIDTH = 32,
    parameter int USER_WIDTH = 1
) (
    input logic aclk,
    input logic aresetn
);
    logic [DATA_WIDTH-1:0]   tdata;
    logic [DATA_WIDTH/8-1:0] tkeep;
    logic                    tvalid;
    logic                    tready;
    logic                    tlast;
    logic [USER_WIDTH-1:0]   tuser;
    
    modport master(output tdata, tkeep, tvalid, tlast, tuser, input tready);
    modport slave(input tdata, tkeep, tvalid, tlast, tuser, output tready);
endinterface
```

### Stream Processing

```systemverilog
module axis_processor (
    input  logic aclk,
    input  logic aresetn,
    axis_if.slave  s_axis,
    axis_if.master m_axis
);

    // Register stage
    logic [31:0] data_reg;
    logic        valid_reg;
    logic        last_reg;
    
    assign s_axis.tready = !valid_reg || m_axis.tready;
    
    always_ff @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            valid_reg <= 1'b0;
        end else begin
            if (s_axis.tready) begin
                valid_reg <= s_axis.tvalid;
                data_reg  <= s_axis.tdata + 1; // Processing
                last_reg  <= s_axis.tlast;
            end
        end
    end
    
    assign m_axis.tdata  = data_reg;
    assign m_axis.tvalid = valid_reg;
    assign m_axis.tlast  = last_reg;
    
endmodule
```

---

## AXI4 (Full)

### Key Signals

| Channel | Signal | Purpose |
|---------|--------|---------|
| AW | awid, awlen, awsize, awburst | Burst info |
| W | wlast | Last beat of burst |
| B | bid | Transaction ID |
| AR | arid, arlen, arsize, arburst | Burst info |
| R | rid, rlast | ID and last |

### Burst Types

| Type | Code | Description |
|------|------|-------------|
| FIXED | 2'b00 | Same address (FIFO) |
| INCR | 2'b01 | Incrementing |
| WRAP | 2'b10 | Wrapping burst |

---

## Protocol Rules

### Handshake

```
VALID must not depend on READY
READY can depend on VALID
Once VALID asserted, must stay high until accepted
```

### Dependencies

```
Write Response depends on:
- Write Address accepted
- Write Data accepted (last)

Read Data depends on:
- Read Address accepted
```

---

## Best Practices

| Practice | Reason |
|----------|--------|
| Register outputs | Better timing |
| Separate read/write FSMs | Simpler logic |
| Handle backpressure | No data loss |
| Check RRESP/BRESP | Error handling |

---

## Anti-patterns (do NOT do this)

1. **Asserting `READY` combinationally from `VALID`.** Creates a combinational loop across the link; many vendor IPs will deadlock or violate the AXI spec rule that `READY` may depend on `VALID` but not vice versa.
2. **Driving `VALID` low after asserting it without a handshake.** AXI requires `VALID` to remain asserted until `READY` is seen.
3. **Reordering responses without `ID` discipline.** AXI4 allows out-of-order completion only when transactions have distinct `AxID`; reordering same-ID responses violates the spec.
4. **Skipping `BRESP`/`RRESP` checks.** Silent SLVERR/DECERR masks real bugs.
5. **AXI4 full for a 32-bit register block.** Use AXI4-Lite — full AXI burst logic is wasted area.

---

## Validation checklist

- [ ] Every channel obeys "VALID stable until READY seen" (lint check or assertion).
- [ ] No combinational path from a channel's `VALID` to its own `READY`.
- [ ] Write response (`B*`) returned only after the last `WLAST` beat is accepted.
- [ ] Read data (`R*`) returned only after `AR*` accepted; `RLAST` matches `ARLEN`.
- [ ] Outstanding transactions limited to declared depth (no unbounded growth).
- [ ] `RRESP`/`BRESP` checked downstream; SLVERR/DECERR propagated, not dropped.
- [ ] AXI-Stream `TLAST` aligned with packet boundary; `TKEEP`/`TSTRB` consistent.
