# VLSI Agent Kit Architecture

> Comprehensive AI Agent Capability Expansion Toolkit for VLSI Development

---

## 📋 Overview

VLSI Agent Kit is a modular system consisting of:

- **14 Specialist Agents** - Role-based AI personas for VLSI domains
- **20 Skills** - Domain-specific knowledge modules
- **10 Workflows** - Slash command procedures

---

## 🏗️ Directory Structure

```plaintext
.agent/
├── ARCHITECTURE.md          # This file
├── agents/                  # 14 Specialist Agents
├── skills/                  # 20 Skills
└── workflows/               # 10 Slash Commands
```

This is the **source payload** that ships inside the npm package. The `vlsi-agkit init` CLI reads from here and generates per-tool installs at the user's project (no `.agent/` is written to user projects — see top-level README "Supported AI Tools").

---

## 🤖 Agents (14)

Specialist AI personas for different VLSI domains.

| Agent | Focus | Skills Used |
| ----- | ----- | ----------- |
| `orchestrator` | Multi-agent coordination | brainstorming, plan-writing |
| `rtl-designer` | RTL design (SV/Verilog/VHDL) | clean-rtl, systemverilog-coding, fsm-design, axi-protocols |
| `verification-engineer` | UVM, formal, coverage | uvm-coding, formal-verification, waveform-debugging |
| `synthesis-engineer` | Logic synthesis | synthesis-guidelines, timing-constraints |
| `timing-analyst` | STA, timing closure | timing-constraints, clock-domain-crossing |
| `fpga-specialist` | Vivado, Quartus, IPs | vivado-flow, quartus-flow, ip-reuse, timing-constraints |
| `asic-specialist` | Synopsys, Cadence | synopsys-flow, cadence-flow, dft-patterns, synthesis-guidelines |
| `physical-design-engineer` | P&R, floorplanning | synopsys-flow, cadence-flow, low-power-design |
| `debugger` | Waveform analysis | waveform-debugging, tcl-scripting |
| `lint-reviewer` | Code quality | clean-rtl |
| `documentation-writer` | Specs, docs | plan-writing, ip-reuse |
| `project-planner` | Task planning | brainstorming, plan-writing |
| `ip-integrator` | IP integration | axi-protocols, ip-reuse |
| `power-analyst` | Power analysis | low-power-design, synopsys-flow, cadence-flow, clean-rtl |

---

## 🧩 Skills (20)

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
| `vivado-flow` | Xilinx Vivado synthesis, impl, ILA/VIO |
| `quartus-flow` | Intel Quartus compile flow, M10K/M20K, DSP |
| `synopsys-flow` | DC, VCS, SpyGlass, DFT Compiler, VC Formal |
| `cadence-flow` | Genus, Xcelium, JasperGold |

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
| `/sta` | Static Timing Analysis (closure + signoff) |
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
| **Total Skills** | 20 |
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
| FPGA Flow | `fpga-specialist` | vivado-flow, quartus-flow |
| ASIC Flow | `asic-specialist` | synopsys-flow, cadence-flow, dft-patterns |
| Debug | `debugger` | waveform-debugging |
| Plan Project | `project-planner` | brainstorming, plan-writing |
