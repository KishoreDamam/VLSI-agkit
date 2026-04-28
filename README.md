# VLSI Agent Kit

> AI Agent templates for VLSI Front-End Development (FPGA & ASIC)

A production-grade collection of skills, agents, and workflows that turn Claude (or any compatible AI coding agent) into a domain-aware VLSI assistant — covering RTL design, verification, synthesis, timing closure, and CDC.

## Quick Install

```bash
npx @kishore-damam/vlsi-agkit init
```

Or install globally:

```bash
npm install -g @kishore-damam/vlsi-agkit
vlsi-agkit init
```

### Manual Installation

Copy the `.agent` folder to your VLSI project root.

## What's Included

| Component     | Count | Description                                                        |
| ------------- | ----- | ------------------------------------------------------------------ |
| **Agents**    | 14    | Specialist AI personas (RTL, Verification, Synthesis, Timing, etc.) |
| **Skills**    | 18    | Domain-specific knowledge modules                                  |
| **Workflows** | 10    | Slash command procedures                                           |

## Skills

Skills are tiered: each has a thin `SKILL.md` index card (≤300 lines) plus deep-dive `references/` and runnable `examples/`.

### Production-grade (Wave 1) ⭐

These six skills ship with full reference docs, compiled examples, validation gates, and citations:

| Skill | Type | What it covers |
|---|---|---|
| `fsm-design` | coding | One/two/three-process FSMs, encoding tradeoffs, timeout counters, SVA assertions |
| `clock-domain-crossing` | flow | 2-FF synchronizers, async FIFO with Gray pointers, handshake CDC, false-path vs max-delay |
| `systemverilog-coding` | coding | `logic`/`reg`/`wire`, interfaces+modports, generate, struct drivers, `always_comb`/`_ff` |
| `timing-constraints` | flow | SDC/XDC: `create_clock`, I/O delays, multicycle paths, Xilinx XDC properties |
| `uvm-coding` | coding | UVM 1.2 components, sequences, TLM analysis ports, dual-FIFO scoreboards, RAL |
| `synthesis-guidelines` | flow | Synthesis-friendly RTL, attributes, retiming, GLS readiness, X-propagation |

### Other skills

| Skill | What it covers |
|---|---|
| `clean-rtl` | RTL coding standards, naming, synthesizable patterns |
| `formal-verification` | Assertions, properties, model checking |
| `waveform-debugging` | Waveform analysis, debug techniques |
| `fpga-flows` | Vivado/Quartus workflows |
| `asic-flows` | Synopsys/Cadence flows |
| `axi-protocols` | AXI4, AXI-Lite, AXI-Stream |
| `low-power-design` | UPF, power gating, clock gating |
| `dft-patterns` | Scan, BIST, ATPG |
| `ip-reuse` | IP packaging, portability |
| `tcl-scripting` | Tcl for EDA tools |
| `brainstorming` | Socratic questioning, architecture exploration |
| `plan-writing` | Task breakdown, plan authoring |

## Usage

### Using Agents

The system automatically detects and applies the right specialist(s):

```
You: "Design a synchronous FIFO with AXI-Stream interface"
AI: 🤖 Applying @rtl-designer + @ip-integrator...

You: "Write UVM testbench for the DMA controller"
AI: 🤖 Using @verification-engineer...

You: "Timing is failing on the CDC path"
AI: 🤖 Using @timing-analyst + @debugger...
```

### Using Workflows

Invoke workflows with slash commands:

| Command        | Description                           |
| -------------- | ------------------------------------- |
| `/brainstorm`  | Architecture exploration              |
| `/plan`        | Project planning                      |
| `/design`      | RTL design workflow                   |
| `/verify`      | Verification workflow                 |
| `/synthesize`  | Synthesis workflow                    |
| `/debug`       | Debug with waveforms                  |
| `/lint`        | Linting workflow                      |
| `/timing`      | Timing analysis                       |
| `/review`      | Code review                           |
| `/integrate`   | IP integration                        |

Example:
```
/design AXI4 memory controller
/verify FIFO with UVM
/timing analyze clock domain crossings
```

## Agent List

| Agent | Focus |
|-------|-------|
| `orchestrator` | Multi-agent coordination |
| `rtl-designer` | RTL design (SV/Verilog/VHDL) |
| `verification-engineer` | UVM, assertions, coverage |
| `synthesis-engineer` | Logic synthesis |
| `timing-analyst` | STA, timing closure |
| `fpga-specialist` | Vivado, Quartus flows |
| `asic-specialist` | Synopsys, Cadence flows |
| `physical-design-engineer` | P&R, floorplanning |
| `debugger` | Waveform analysis |
| `lint-reviewer` | Code quality |
| `documentation-writer` | Specs, docs |
| `project-planner` | Task planning |
| `ip-integrator` | IP, bus protocols |
| `power-analyst` | Power analysis, UPF |

## Skill structure

Each Wave 1 skill follows a tiered layout:

```
.agent/skills/<skill-name>/
├── SKILL.md            # Index card — when to use, core patterns, anti-patterns (≤300 lines)
├── references/         # Deep-dive markdown for each topic
│   ├── <topic>.md
│   └── ...
└── examples/           # Compilable / runnable worked examples
    ├── <example>.sv
    ├── tb_<example>.sv # Self-checking testbench (where applicable)
    └── Makefile        # Tier-aware verification recipe
```

### Skill verification tiers

The `Makefile` in each `examples/` folder declares a tier that controls how `make verify` treats it:

| Tier | Meaning |
|---|---|
| `build-sim` | Compile + run simulation (iverilog or vendor sim); self-checking testbench reports PASS/FAIL |
| `build-only` | Compile-only (syntax check); some examples need vendor library at sim time |
| `needs-vendor-sim` | Skipped on iverilog; requires Questa/VCS/Xcelium (e.g., UVM, SystemVerilog interfaces) |
| `tool-output` | Not compilable (XDC/SDC, synthesis reports); skipped in CI |
| `manual-review` | Reference-only; not auto-verified |

## Verifying skills locally

```bash
make help          # Show all targets
make list-skills   # Print discovered skill list (skips _-prefixed dirs)
make verify        # Run every skill's examples/Makefile verify target
```

**Skill discovery:** any subdirectory of `.agent/skills/` is treated as a
skill, except names starting with `_` (reserved for templates and tooling).

**Simulator selection:** the verify rules use `tools.mk` to pick a simulator
in this order:
1. `iverilog` on PATH (default for CI / open-source flows)
2. `VLSI_SIM` env var (e.g. `VLSI_SIM=xsim` for Vivado xsim)
3. `VLSI_SIM_BIN` for fully-qualified path overrides
4. `.agent/tools.local.mk` (per-user, gitignored — see `tools.example.mk`)

To use a vendor simulator without polluting PATH:
```bash
cp tools.example.mk .agent/tools.local.mk
# Edit .agent/tools.local.mk to point at your Vivado/VCS/Questa install
make verify
```

## Documentation

See [ARCHITECTURE.md](.agent/ARCHITECTURE.md) for the full architecture, agent responsibilities, and skill-loading protocol.

## Acknowledgements

This kit is based on the [Antigravity Kit](https://github.com/vudovn/antigravity-kit) by [@vudovn](https://github.com/vudovn).
The structure and agentic patterns were adapted for the VLSI domain.

## License

MIT
