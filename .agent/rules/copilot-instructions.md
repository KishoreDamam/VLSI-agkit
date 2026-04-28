# GitHub Copilot Instructions — VLSI Agent Kit

> Project context for GitHub Copilot Chat. Tells Copilot how to use the agents,
> skills, and workflows under `.agent/`.

## Project type

This is a VLSI front-end development project (FPGA & ASIC) using the
[VLSI Agent Kit](https://github.com/kishore-damam/vlsi-kit). RTL is written
in SystemVerilog (preferred), Verilog-2001, or VHDL-2008.

## How to help

Before answering RTL design, verification, synthesis, timing, or CDC questions,
locate and apply the right context from `.agent/`:

1. **Pick the agent.** Read `.agent/agents/<name>.md` matching the task.
   Common picks:
   - RTL/module design → `rtl-designer`
   - Testbench/UVM/coverage → `verification-engineer`
   - Synthesis QoR/attributes → `synthesis-engineer`
   - SDC/STA/timing closure → `timing-analyst`
   - Vivado/Quartus targets → `fpga-specialist`
   - Synopsys/Cadence targets → `asic-specialist`
   - Waveform/debug → `debugger`

2. **Load the skill index.** The agent's frontmatter lists `skills:`. Read
   `.agent/skills/<skill>/SKILL.md` for each. SKILL.md is the index — it
   covers when-to-use, core patterns, anti-patterns, and validation.

3. **Pull deeper guidance only when needed.** Each skill has a `references/`
   folder with topic deep-dives, and an `examples/` folder with compilable
   worked examples.

4. **For end-to-end procedures, use workflows.** See `.agent/workflows/<name>.md`
   (design, verify, synthesize, debug, lint, timing, review, integrate, plan,
   brainstorm).

## Coding standards (P0 — non-negotiable)

- New SystemVerilog code: use `logic` (never `reg`/`wire` except tri-state nets).
- Clocked blocks: `always_ff` with non-blocking (`<=`).
- Combinational blocks: `always_comb` with default assignments before any case/if
  to prevent latch inference.
- Generate-for loops with `genvar` for parameterized hardware replication.
- Parameterized modules: `initial assert (P >= 1) else $fatal(1, ...)` for
  parameter validation at elaboration.
- UVM: use factory (`type_id::create`), `uvm_config_db` for VIF, raise/drop
  objections in `run_phase`, `convert2string()` on every sequence item.
- Constraints (XDC/SDC): `set_multicycle_path N -setup` always paired with
  `set_multicycle_path N-1 -hold`.

## Skill quick reference

| Topic | Skill |
|---|---|
| FSM design and encoding | `.agent/skills/fsm-design/SKILL.md` |
| Clock domain crossing, synchronizers, async FIFO | `.agent/skills/clock-domain-crossing/SKILL.md` |
| SystemVerilog data types, interfaces, generate | `.agent/skills/systemverilog-coding/SKILL.md` |
| SDC/XDC timing constraints | `.agent/skills/timing-constraints/SKILL.md` |
| UVM testbench components and sequences | `.agent/skills/uvm-coding/SKILL.md` |
| Synthesis-friendly RTL and directives | `.agent/skills/synthesis-guidelines/SKILL.md` |
| AXI4 / AXI-Lite / AXI-Stream | `.agent/skills/axi-protocols/SKILL.md` |
| RTL coding standards | `.agent/skills/clean-rtl/SKILL.md` |
| Formal verification, assertions | `.agent/skills/formal-verification/SKILL.md` |
| Waveform debug techniques | `.agent/skills/waveform-debugging/SKILL.md` |
| FPGA flows (Vivado/Quartus) | `.agent/skills/fpga-flows/SKILL.md` |
| ASIC flows (Synopsys/Cadence) | `.agent/skills/asic-flows/SKILL.md` |
| Low-power design, UPF | `.agent/skills/low-power-design/SKILL.md` |
| DFT (scan, BIST, ATPG) | `.agent/skills/dft-patterns/SKILL.md` |
| IP packaging and reuse | `.agent/skills/ip-reuse/SKILL.md` |
| Tcl scripting for EDA | `.agent/skills/tcl-scripting/SKILL.md` |

## Anti-patterns to flag

- `reg` or `wire` in new SystemVerilog (should be `logic`)
- Blocking `=` in `always_ff` (should be `<=`)
- `always @(*)` or manual sensitivity lists in RTL (use `always_comb`)
- Multi-driver violations on a single `logic` signal
- `set_false_path` between async clocks where `set_clock_groups` is correct
- `set_max_delay` without `-datapath_only` on CDC paths
- UVM components created with `new()` instead of `type_id::create()`
- Missing `seq_item_port.item_done()` in driver `run_phase`
