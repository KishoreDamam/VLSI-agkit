---
name: ip-reuse
description: IP packaging, parameterization, and portability.
---

# IP Reuse

> Design IPs for reusability across projects.

---

## IP Package Structure

```
my_ip/
├── rtl/              # RTL source
│   ├── my_ip.sv
│   └── submodules/
├── tb/               # Testbench
│   ├── tb_my_ip.sv
│   └── sequences/
├── constraints/      # SDC files
├── doc/              # Documentation
│   ├── my_ip_spec.md
│   └── my_ip_prm.md  # Programmer's manual
├── scripts/          # Build scripts
└── README.md
```

---

## Parameterization

```systemverilog
module my_ip #(
    // Width parameters
    parameter int DATA_WIDTH = 32,
    parameter int ADDR_WIDTH = 16,
    
    // Feature enables
    parameter bit ENABLE_PARITY = 1'b0,
    parameter bit ENABLE_ECC    = 1'b0,
    
    // Derived (localparam)
    localparam int DATA_BYTES = DATA_WIDTH / 8
) (
    // Ports with parameterized widths
    input  logic [DATA_WIDTH-1:0] data_in,
    output logic [DATA_WIDTH-1:0] data_out
);
```

---

## Interface Abstraction

### Use Standard Interfaces

```systemverilog
module my_ip (
    input  logic clk,
    input  logic rst_n,
    
    // Standard AXI-Stream
    axis_if.slave  s_axis,
    axis_if.master m_axis,
    
    // Standard AXI-Lite for config
    axi_lite_if.slave s_axil
);
```

### Wrapper for Non-Standard

```systemverilog
module my_ip_wrapper (
    // Exploded interface for legacy
    input  logic [31:0] tdata,
    input  logic        tvalid,
    output logic        tready
);
    // Internal interface
    axis_if axis_internal(...);
    
    // Connect
    assign axis_internal.tdata = tdata;
    // ...
    
    my_ip u_ip (.s_axis(axis_internal), ...);
endmodule
```

---

## Documentation Template

```markdown
# [IP Name] Specification

## Overview
[What this IP does]

## Features
- Feature 1
- Feature 2

## Parameters
| Parameter | Default | Description |
|-----------|---------|-------------|
| DATA_WIDTH | 32 | Data bus width |

## Interfaces
| Interface | Type | Description |
|-----------|------|-------------|
| s_axis | AXI-Stream Slave | Data input |

## Resource Usage
| Resource | Utilization |
|----------|-------------|
| LUTs | ~500 |
| Registers | ~300 |

## Timing
- Tested at 250 MHz on xc7a100t
```

---

## Checklist for Reusable IP

- [ ] Fully parameterized
- [ ] No hardcoded values
- [ ] Standard interfaces
- [ ] Self-contained (no external deps)
- [ ] Documented parameters
- [ ] Example testbench
- [ ] Constraints included
- [ ] Lint clean
