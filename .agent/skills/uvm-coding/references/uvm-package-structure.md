# UVM Package & Directory Structure

> A UVM testbench's package layout determines compile order, namespace
> hygiene, and reusability. This reference captures the cookbook's
> recommended package hierarchy and file organization.

## Why packages matter

UVM testbenches are made of dozens of files. Compile-time issues fall
into three buckets:

- **Order errors**: file A imports a type that file B defines, but
  file B compiles second.
- **Namespace collisions**: two agents both define `my_driver`.
- **Coupling**: changing one file forces a re-build of everything.

Packages solve all three when used systematically. The cookbook
defines five package tiers.

## Five package tiers

```
Test package        (tests, scenarios)
       │ imports
       ▼
Sequence packages   (per-agent: API + worker sequences)
       │ imports
       ▼
Env package         (top-level env, scoreboards, virtual sequencer, config)
       │ imports
       ▼
Agent packages      (one per protocol: driver, monitor, sequencer, agent)
       │ imports
       ▼
Utility packages    (shared types, parameters, base classes)
```

### Agent package — the smallest unit of reuse

One package per protocol agent:

```systemverilog
// File: apb_agent_pkg.sv
package apb_agent_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    // Order matters within the package
    `include "apb_seq_item.sv"
    `include "apb_driver.sv"
    `include "apb_monitor.sv"
    `include "apb_sequencer.sv"
    `include "apb_agent_config.sv"
    `include "apb_agent.sv"
endpackage
```

Everything an agent needs is in this one package. To use the agent:

```systemverilog
import apb_agent_pkg::*;
```

That's it — no individual file imports.

### Sequence package — per-agent stimulus library

```systemverilog
// File: apb_sequences_pkg.sv
package apb_sequences_pkg;
    import uvm_pkg::*;
    import apb_agent_pkg::*;
    `include "uvm_macros.svh"

    `include "apb_base_seq.sv"
    `include "apb_write_seq.sv"
    `include "apb_read_seq.sv"
    `include "apb_burst_seq.sv"
endpackage
```

Separating the sequence package from the agent package allows tests to
import sequences without forcing test-only types into the agent.

### Env package — system-level integration

```systemverilog
// File: chip_env_pkg.sv
package chip_env_pkg;
    import uvm_pkg::*;
    import apb_agent_pkg::*;
    import spi_agent_pkg::*;
    import apb_sequences_pkg::*;
    import spi_sequences_pkg::*;
    `include "uvm_macros.svh"

    `include "chip_env_config.sv"
    `include "chip_virtual_sequencer.sv"
    `include "chip_scoreboard.sv"
    `include "chip_predictor.sv"
    `include "chip_env.sv"
endpackage
```

### Test package — test cases and virtual sequences

```systemverilog
// File: chip_test_pkg.sv
package chip_test_pkg;
    import uvm_pkg::*;
    import chip_env_pkg::*;
    `include "uvm_macros.svh"

    `include "chip_base_test.sv"
    `include "chip_smoke_test.sv"
    `include "chip_stress_test.sv"
    `include "chip_init_vseq.sv"
    `include "chip_stress_vseq.sv"
endpackage
```

### Utility package — shared low-level pieces

For things multiple agents need (e.g., a shared `address_t` typedef,
project-wide parameters):

```systemverilog
// File: chip_params_pkg.sv
package chip_params_pkg;
    parameter int ADDR_WIDTH = 32;
    parameter int DATA_WIDTH = 64;
    typedef logic [ADDR_WIDTH-1:0] addr_t;
    typedef logic [DATA_WIDTH-1:0] data_t;
endpackage
```

Utility packages should have *no* UVM dependencies (no `import
uvm_pkg`) — they're meant to be importable by RTL and by the
testbench.

## Directory structure (cookbook recommendation)

```
project/
├── rtl/
│   └── ...
├── tb/
│   ├── packages/
│   │   ├── chip_params_pkg.sv
│   │   └── chip_test_pkg.sv               ← top-level test package
│   ├── env/
│   │   ├── chip_env_pkg.sv                ← env package + includes
│   │   ├── chip_env.sv
│   │   ├── chip_env_config.sv
│   │   ├── chip_virtual_sequencer.sv
│   │   ├── chip_scoreboard.sv
│   │   └── chip_predictor.sv
│   ├── tests/
│   │   ├── chip_base_test.sv
│   │   ├── chip_smoke_test.sv
│   │   └── chip_init_vseq.sv
│   ├── apb_agent/
│   │   ├── apb_agent_pkg.sv               ← agent package
│   │   ├── apb_seq_item.sv
│   │   ├── apb_driver.sv
│   │   ├── apb_monitor.sv
│   │   ├── apb_sequencer.sv
│   │   ├── apb_agent.sv
│   │   ├── apb_agent_config.sv
│   │   ├── apb_if.sv                       ← interface (not in package)
│   │   └── sequences/
│   │       ├── apb_sequences_pkg.sv        ← sequence package
│   │       ├── apb_base_seq.sv
│   │       ├── apb_write_seq.sv
│   │       └── apb_read_seq.sv
│   ├── spi_agent/
│   │   └── ... (parallel to apb_agent/)
│   └── top/
│       ├── hdl_top.sv                       ← DUT + BFMs + interfaces
│       └── tb_top.sv                        ← run_test() initial block
└── sim/
    ├── compile.f                             ← file list, in dependency order
    └── Makefile
```

### File naming

| What | File name |
|---|---|
| Package | `<thing>_pkg.sv` (always `_pkg` suffix) |
| Class | `<class_name>.sv` (matching class name 1:1) |
| Interface | `<thing>_if.sv` |
| Top-level module | `hdl_top.sv`, `tb_top.sv` |
| Includes (UVM) | `*.svh` is acceptable but cookbook prefers `.sv` |

One class per file. The file name matches the class name. This makes
`grep` work and keeps editor navigation predictable.

### Directory naming

Cookbook recommendation: short, lowercase, hyphen-free.

| Recommended | Avoid |
|---|---|
| `apb_agent/` | `apbAgent/`, `APB_Agent/`, `apb-agent/` |
| `sequences/` | `seqs/`, `stimuli/` |
| `tests/` | `tc/`, `testcases/` |

## Package imports — the rules

1. **Import at package top.** Never inside a class.
2. **Import `uvm_pkg` first**, then `` `include "uvm_macros.svh" ``.
3. **`include` files within the package**, after all imports.
4. **Use `import pkg::*`** for normal use; `import pkg::specific_t`
   only for namespace conflict resolution.
5. **A package never includes another package's files** — always
   `import`.

## Compile order

Compile in dependency order. The file list (`compile.f` or
similar):

```
# Utility packages first
tb/packages/chip_params_pkg.sv

# Agent packages — order doesn't matter between them
tb/apb_agent/apb_agent_pkg.sv
tb/spi_agent/spi_agent_pkg.sv

# Sequence packages — depend on their agent
tb/apb_agent/sequences/apb_sequences_pkg.sv
tb/spi_agent/sequences/spi_sequences_pkg.sv

# Env package
tb/env/chip_env_pkg.sv

# Test package — top
tb/packages/chip_test_pkg.sv

# Top-level modules
tb/top/hdl_top.sv
tb/top/tb_top.sv
```

When agents are added, only their package needs to be added to the
file list. The env and test packages just import the new agent's
package.

## Namespace hygiene

Use a project-wide prefix to prevent global namespace collisions:

```systemverilog
// Bad — generic name
class driver extends uvm_driver #(item);
endclass

// Good — protocol-prefixed
class apb_driver extends uvm_driver #(apb_seq_item);
endclass
```

Within a package, short names are fine. Across packages, prefix.

The cookbook also recommends a company / project prefix on
package-spanning concepts:

```systemverilog
// Generic name from a vendor library — could collide
package agent_pkg;

// Project-scoped — never collides
package mychip_apb_agent_pkg;
```

## Common pitfalls

- **Including `.sv` files from multiple packages.** Forward declares,
  duplicate definitions, recompile thrashing. One file lives in one
  package only.
- **Using `` `include "uvm_macros.svh" `` without first importing
  `uvm_pkg`.** Macros expand to references to `uvm_pkg::*` types.
- **Importing a class file directly instead of its package.** Bypasses
  the package's dependency declaration; works until someone adds a
  type the file needs.
- **Cyclic package dependencies.** `apb_agent_pkg` imports
  `chip_env_pkg` which imports `apb_agent_pkg`. Compile failure.
  Always: low-level → high-level, never reverse.
- **`*.svh` files with `module`/`interface` declarations.** Header files
  should contain only class includes; modules belong in `.sv` files
  outside packages.
- **Putting interfaces in the agent package.** Interfaces are not
  classes — they need to be compiled at the elaborated module scope.
  Keep them outside the package.

## Citations

- **Mentor Graphics UVM Cookbook**, *SystemVerilog Packages* / *Package
  Definitions* / *Coding Guidelines* — package hierarchy,
  directory structure, file naming, namespace recommendations.
- **Accellera UVM 1.2 §5** — package usage conventions.

## See also

- `component-architecture.md` — virtual interface in a package vs
  raw interface.
- `two-kingdoms-emulation.md` — separate compilation of `hdl_top`
  and `tb_top`.
- `analysis-ports-and-scoreboards.md` — env package contents.
