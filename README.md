# VLSI Agent Kit

> AI Agent templates for VLSI Front-End Development (FPGA & ASIC)

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

## Verifying skills locally

Each skill that ships a worked example under `examples/` includes a `Makefile`
that builds, simulates, or lints the example end-to-end. The repo root
`Makefile` walks every skill and runs each `examples/Makefile` in turn.

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

See [ARCHITECTURE.md](.agent/ARCHITECTURE.md) for full details.

## Acknowledgements

This kit is based on the [Antigravity Kit](https://github.com/vudovn/antigravity-kit) by [@vudovn](https://github.com/vudovn).
The structure and agentic patterns were adapted for the VLSI domain.

## License

MIT
