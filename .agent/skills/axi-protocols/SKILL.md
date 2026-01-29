---
name: axi-protocols
description: AXI4, AXI4-Lite, and AXI4-Stream bus protocols.
---

# AXI Protocols

> ARM AMBA AXI bus protocol patterns.

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
