# VLSI Agent Kit

> AI Agent templates for VLSI Front-End Development (FPGA & ASIC)

## Quick Install

```bash
npx @kishore-damam/vlsi-agkit init
```

You'll be prompted to:
1. Pick a **role profile** (Full Stack, FPGA Engineer, ASIC Engineer, Verification Engineer, RTL Designer, or Physical Design).
2. Pick one or more **target tools**:

| Tool | Output |
|---|---|
| Claude Code | `.claude/agents/`, `.claude/commands/`, `CLAUDE.md` |
| Gemini CLI | `GEMINI.md` |
| VS Code / Copilot | `.github/copilot-instructions.md` |
| Antigravity | `.agent/` (legacy layout) |
| Cursor | `.cursor/rules/*.mdc` |
| Windsurf | `.windsurf/rules/*.md` |

### Non-interactive / scripted install

```bash
npx @kishore-damam/vlsi-agkit init \
  --role fpga-engineer \
  --tools claude,cursor \
  --dir ./my-project
```

See `vlsi-agkit init --list-profiles` and `vlsi-agkit init --list-tools` for available ids.

### Migration from 1.0.x

1.0.x always installed `.agent/` + `GEMINI.md`. For equivalent behavior:
```bash
vlsi-agkit init --role full-stack --tools antigravity,gemini
```

## What's Included

| Component     | Count | Description                                                        |
| ------------- | ----- | ------------------------------------------------------------------ |
| **Agents**    | 14    | Specialist AI personas (RTL, Verification, Synthesis, Timing, etc.) |
| **Skills**    | 22    | Domain-specific knowledge modules                                  |
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

## Documentation

See [ARCHITECTURE.md](.agent/ARCHITECTURE.md) for full details.

## Acknowledgements

This kit is based on the [Antigravity Kit](https://github.com/vudovn/antigravity-kit) by [@vudovn](https://github.com/vudovn).
The structure and agentic patterns were adapted for the VLSI domain.

## License

MIT
