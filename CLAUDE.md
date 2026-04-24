# VLSI Agent Kit - Claude Code Configuration

> Comprehensive AI Agent Capability Expansion Toolkit for VLSI Development

## Agent & Skill Protocol

Before performing any VLSI implementation, read the appropriate agent file from `.agent/agents/` and its associated skills from `.agent/skills/` to load domain-specific knowledge.

### Modular Skill Loading

1. Analyze user request to determine the domain
2. Select the appropriate agent from `.agent/agents/`
3. Read the agent's frontmatter to identify required skills
4. Read relevant `SKILL.md` files from `.agent/skills/`
5. Apply the loaded knowledge to generate the response

**Rule Priority:** CLAUDE.md (P0) > Agent .md (P1) > SKILL.md (P2). All rules are binding.

---

## Request Classifier

Before any action, classify the request:

| Request Type | Trigger Keywords | Result |
|---|---|---|
| **Question** | "what is", "how does", "explain" | Text response |
| **Survey/Intel** | "analyze", "review", "check" | Analysis report |
| **Simple RTL** | "fix", "add signal", "change" (single file) | Inline edit |
| **Complex RTL** | "design", "implement", "create module" | Full workflow |
| **Verification** | "testbench", "UVM", "verify" | Full workflow |

---

## Agent Routing

Automatically select the best specialist based on the domain:

| Domain | Agent File | Trigger Keywords |
|---|---|---|
| RTL Design | `rtl-designer.md` | module, design, implement, FSM, register, logic |
| Verification | `verification-engineer.md` | testbench, UVM, coverage, assertion, verify |
| Synthesis | `synthesis-engineer.md` | synthesize, optimize, area, timing, constraints |
| Timing | `timing-analyst.md` | STA, timing, clock, setup, hold, path |
| FPGA | `fpga-specialist.md` | Vivado, Quartus, FPGA, bitstream, IP |
| ASIC | `asic-specialist.md` | ASIC, Synopsys, Cadence, tapeout, DFT |
| Debug | `debugger.md` | debug, waveform, trace, not working, fails |
| CDC | `timing-analyst.md` | CDC, clock domain, synchronizer, metastability |
| Power | `power-analyst.md` | power, UPF, clock gating, leakage |
| Integration | `ip-integrator.md` | AXI, bus, integrate, interconnect, bridge |
| Lint | `lint-reviewer.md` | lint, code quality, naming, style |
| Documentation | `documentation-writer.md` | document, spec, datasheet, register map |
| Planning | `project-planner.md` | plan, schedule, breakdown, milestone |
| Multi-domain | `orchestrator.md` | complex tasks spanning multiple domains |

---

## Universal Rules (Always Active)

### Clean RTL (Global Mandatory)

ALL RTL code MUST follow `.agent/skills/clean-rtl/SKILL.md` rules:

- **Naming**: `i_`/`o_` port prefixes, `clk`/`rst_n` conventions, `UPPER_CASE` params, `name_t` typedefs, `u_` instances
- **Style**: Consistent indentation, one statement per line
- **Sequential**: `always_ff`, non-blocking (`<=`), reset all registers
- **Combinational**: `always_comb`, blocking (`=`), default all outputs first
- **No latches**: Complete if/else, default in case, assign defaults before logic
- **Assertions**: Add inline assertions for critical paths

### File Dependency Awareness

Before modifying ANY file:
1. Check module hierarchy
2. Identify instantiating modules
3. Update ALL affected files together

### Socratic Gate

For complex requests, ask clarifying questions first:

| Unclear Aspect | Question |
|---|---|
| Interface | "What bus protocol? (AXI4, AXI-Lite, AXI-Stream, Wishbone?)" |
| Clock Domains | "How many clock domains? Any CDC requirements?" |
| Target | "FPGA or ASIC? Which device/process?" |
| Performance | "What's the target frequency? Latency requirements?" |
| Area | "Any area constraints? Resource limits?" |

---

## RTL Rules (When Writing Code)

### Project Type Routing

| Project Type | Primary Agent | Skills |
|---|---|---|
| FPGA | `fpga-specialist` | fpga-flows, timing-constraints |
| ASIC | `asic-specialist` | asic-flows, dft-patterns |
| IP Design | `rtl-designer` | clean-rtl, ip-reuse |
| Verification | `verification-engineer` | uvm-patterns |

### Final Checklist Protocol

When user says "run checks", "final verification", or "pre-synthesis":

Priority execution order: Lint → CDC → Reset → Timing → Coverage

---

## Verification Rules

- Follow `.agent/skills/uvm-patterns/SKILL.md` for all UVM testbenches
- Mandatory components: Sequencer, Driver, Monitor, Scoreboard
- Use factory for object creation
- Coverage-driven verification
- Follow `.agent/skills/formal-verification/SKILL.md` for assertions

---

## Available Slash Commands

| Command | Description |
|---|---|
| `/brainstorm` | Architecture exploration and requirements gathering |
| `/plan` | Project planning and task breakdown |
| `/design` | RTL design workflow |
| `/verify` | Verification workflow |
| `/synthesize` | Synthesis workflow |
| `/debug` | Debug with waveform analysis |
| `/lint` | RTL linting workflow |
| `/timing` | Timing analysis and closure |
| `/review` | RTL code review |
| `/integrate` | IP integration workflow |

---

## Skills Reference

Skills are loaded on-demand from `.agent/skills/`. Key skills by category:

**RTL & Language:** clean-rtl, systemverilog-patterns, fsm-design
**Verification:** uvm-patterns, formal-verification, waveform-debugging
**Synthesis & Timing:** synthesis-guidelines, timing-constraints, clock-domain-crossing
**Design Techniques:** low-power-design, dft-patterns, axi-protocols
**Flows:** fpga-flows, asic-flows
**Tools & Process:** tcl-scripting, ip-reuse, brainstorming, plan-writing

---

## Quick Reference

| Need | Agent | Skills |
|---|---|---|
| Design RTL | `rtl-designer` | clean-rtl, systemverilog-patterns |
| Verify Design | `verification-engineer` | uvm-patterns, formal-verification |
| Synthesize | `synthesis-engineer` | synthesis-guidelines |
| Fix Timing | `timing-analyst` | timing-constraints, clock-domain-crossing |
| FPGA Flow | `fpga-specialist` | fpga-flows |
| ASIC Flow | `asic-specialist` | asic-flows, dft-patterns |
| Debug | `debugger` | waveform-debugging |
| Plan Project | `project-planner` | brainstorming, plan-writing |
