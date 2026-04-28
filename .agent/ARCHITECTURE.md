# VLSI Agent Kit Architecture

> Comprehensive AI Agent Capability Expansion Toolkit for VLSI Development

---

## 📋 Overview

VLSI Agent Kit is a modular system consisting of:

- **14 Specialist Agents** - Role-based AI personas for VLSI domains
- **18 Skills** - Domain-specific knowledge modules
- **10 Workflows** - Slash command procedures

---

## 🏗️ Directory Structure

```plaintext
.agent/
├── ARCHITECTURE.md          # This file
├── agents/                  # 14 Specialist Agents
├── skills/                  # 18 Skills
├── workflows/               # 10 Slash Commands
├── rules/                   # Global Rules
└── scripts/                 # Validation Scripts
```

---

## 🤖 Agents (14)

Specialist AI personas for different VLSI domains.

| Agent | Focus | Skills Used |
| ----- | ----- | ----------- |
| `orchestrator` | Multi-agent coordination | brainstorming, plan-writing |
| `rtl-designer` | RTL design (SV/Verilog/VHDL) | clean-rtl, systemverilog-coding, fsm-design |
| `verification-engineer` | UVM, formal, coverage | uvm-coding, formal-verification |
| `synthesis-engineer` | Logic synthesis | synthesis-guidelines, timing-constraints |
| `timing-analyst` | STA, timing closure | timing-constraints, clock-domain-crossing |
| `fpga-specialist` | Vivado, Quartus, IPs | fpga-flows, ip-reuse |
| `asic-specialist` | Synopsys, Cadence | asic-flows, dft-patterns |
| `physical-design-engineer` | P&R, floorplanning | asic-flows, low-power-design |
| `debugger` | Waveform analysis | waveform-debugging, tcl-scripting |
| `lint-reviewer` | Code quality | clean-rtl |
| `documentation-writer` | Specs, docs | - |
| `project-planner` | Task planning | brainstorming, plan-writing |
| `ip-integrator` | IP integration | axi-protocols, ip-reuse |
| `power-analyst` | Power analysis | low-power-design |

---

## 🧩 Skills (18)

Modular knowledge domains that agents can load on-demand.

### RTL & Language

| Skill | Description |
| ----- | ----------- |
| `clean-rtl` | RTL coding standards, naming, synthesizable patterns |
| `systemverilog-coding` | SV2017 data types, interfaces, generate, always blocks |
| `fsm-design` | State machine patterns, encoding, assertions |

### Verification

| Skill | Description |
| ----- | ----------- |
| `uvm-coding` | UVM components, sequences, TLM ports, RAL, phasing |
| `formal-verification` | Assertions, properties, model checking |
| `waveform-debugging` | Waveform analysis, debug techniques |

### Synthesis & Implementation

| Skill | Description |
| ----- | ----------- |
| `synthesis-guidelines` | Synthesis-friendly RTL, directives, timing optimization, GLS |
| `timing-constraints` | SDC/XDC, clocks, I/O delays, multicycle paths |
| `fpga-flows` | Vivado/Quartus workflows |
| `asic-flows` | Synopsys/Cadence flows |

### Design Techniques

| Skill | Description |
| ----- | ----------- |
| `clock-domain-crossing` | CDC synchronizers, async FIFO, false-path vs max-delay |
| `axi-protocols` | AXI4, AXI-Lite, AXI-Stream |

### Advanced Topics

| Skill | Description |
| ----- | ----------- |
| `low-power-design` | UPF, power gating, clock gating |
| `dft-patterns` | Scan, BIST, ATPG |
| `ip-reuse` | IP packaging, portability |

### Tools & Process

| Skill | Description |
| ----- | ----------- |
| `tcl-scripting` | Tcl for EDA tools |
| `brainstorming` | Socratic questioning |
| `plan-writing` | Task breakdown |

---

## 🔄 Workflows (10)

Slash command procedures. Invoke with `/command`.

| Command | Description |
| ------- | ----------- |
| `/brainstorm` | Architecture exploration |
| `/plan` | Project planning |
| `/design` | RTL design workflow |
| `/verify` | Verification workflow |
| `/synthesize` | Synthesis workflow |
| `/debug` | Debug with waveforms |
| `/lint` | Linting workflow |
| `/timing` | Timing analysis |
| `/review` | Code review |
| `/integrate` | IP integration |

---

## 🎯 Skill Loading Protocol

```plaintext
User Request → Skill Description Match → Load SKILL.md
                                            ↓
                                    Read references/
                                            ↓
                                    Execute if needed
```

### Skill Structure

```plaintext
skill-name/
├── SKILL.md           # (Required) Metadata & instructions
├── templates/         # (Optional) Code templates
└── references/        # (Optional) Docs, examples
```

---

## 📊 Statistics

| Metric | Value |
| ------ | ----- |
| **Total Agents** | 14 |
| **Total Skills** | 18 |
| **Total Workflows** | 10 |
| **Coverage** | FPGA + ASIC front-end |

---

## 🔗 Quick Reference

| Need | Agent | Skills |
| ---- | ----- | ------ |
| Design RTL | `rtl-designer` | clean-rtl, systemverilog-coding |
| Verify Design | `verification-engineer` | uvm-coding, formal-verification |
| Synthesize | `synthesis-engineer` | synthesis-guidelines |
| Fix Timing | `timing-analyst` | timing-constraints, clock-domain-crossing |
| FPGA Flow | `fpga-specialist` | fpga-flows |
| ASIC Flow | `asic-specialist` | asic-flows, dft-patterns |
| Debug | `debugger` | waveform-debugging |
| Plan Project | `project-planner` | brainstorming, plan-writing |
