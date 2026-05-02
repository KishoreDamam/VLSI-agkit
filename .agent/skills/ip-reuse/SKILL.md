---
name: ip-reuse
description: Use when packaging a reusable IP block — directory layout, parameterization, standard-interface wrappers (AXI/Avalon), documentation templates, or reviewing portability before reuse across projects.
---

# IP Reuse

> Design IPs for reusability across projects.

---

## When to use

- Packaging an internally-developed block for use in another project or by another team.
- Promoting a one-off RTL module into a parameterized library component.
- Reviewing a third-party IP before integration (checking the contract it exposes).
- Writing the README/spec/timing docs that go with delivered IP.

**Not for:** project-specific wrappers that won't be reused (don't pay the abstraction tax); FPGA IP-block flows that bind to a vendor IP catalog (use Vivado IP Packager / Quartus IP Catalog).

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

## Anti-patterns (do NOT do this)

1. **Hardcoded widths / depths.** `parameter` everything that might vary (data width, address width, FIFO depth, reset polarity).
2. **Project-specific clock or reset names baked into the IP.** Use generic `clk`/`rst_n` ports and let the integrator connect.
3. **`include "rtl/foo.svh"` with absolute project paths.** Use relative `+incdir` or pure-package definitions.
4. **Mixing AXI4 and AXI4-Lite without separate wrapper modules.** Integrators want one interface per port, not a parameter that switches protocol.
5. **No example testbench or constraints file.** The first integrator becomes the involuntary first verifier — they will not be happy.
6. **Bumping the IP version without a changelog.** Downstream users can't tell breaking changes from bug fixes.

---

## Validation checklist (for releasing reusable IP)

- [ ] Fully parameterized; no hardcoded magic numbers in the RTL.
- [ ] All ports use standard interfaces (AXI/Avalon/AXI-Stream) or are explicitly documented.
- [ ] Self-contained: no external `+incdir` outside the IP root.
- [ ] Every parameter documented (range, default, effect).
- [ ] Example testbench compiles and runs PASS on a known simulator.
- [ ] Synthesis-ready constraints (SDC) included; lint clean against project ruleset.
- [ ] README covers: features, parameters, interfaces, resource estimates, timing assumptions.
- [ ] Versioned (semver) with a CHANGELOG entry for every release.
