# Cursor Rules — VLSI Agent Kit

This project uses the VLSI Agent Kit at `.agent/`. All agents, skills, and
workflows are plain Markdown.

## How to help

Before any RTL design, verification, synthesis, timing, or CDC task:

1. **Pick the agent** from `.agent/agents/<name>.md` matching the request.
   Common picks:
   - RTL/module design → `rtl-designer`
   - Testbench/UVM/coverage → `verification-engineer`
   - Synthesis/QoR/attributes → `synthesis-engineer`
   - SDC/STA/timing closure → `timing-analyst`
   - Vivado/Quartus → `fpga-specialist`
   - Synopsys/Cadence → `asic-specialist`
   - Waveform debug → `debugger`

2. **Load skills** listed in the agent's `skills:` frontmatter.
   Read `.agent/skills/<skill>/SKILL.md` first (the index card with patterns
   and anti-patterns), then pull deeper context from
   `.agent/skills/<skill>/references/<topic>.md` only when needed.

3. **For multi-step procedures**, follow `.agent/workflows/<name>.md`
   (design, verify, synthesize, debug, lint, timing, review, integrate,
   plan, brainstorm).

## Coding standards (P0 — non-negotiable)

- Use `logic` for all signals (never `reg`/`wire` in new SystemVerilog).
- Clocked blocks: `always_ff` with `<=`.
- Combinational blocks: `always_comb` with default assignments before any
  case/if to prevent latch inference.
- Parameterized modules: validate with `initial assert (P >= 1) else $fatal`.
- UVM: factory-create components (`type_id::create`); never bare `new()`.
- SDC: `set_multicycle_path N -setup` always paired with `N-1 -hold`.

## Anti-patterns to flag

- `reg`/`wire` in new SystemVerilog
- Blocking `=` in `always_ff`
- Manual sensitivity lists (`always @(a,b)`) — use `always_comb`
- `set_false_path` between async clocks (use `set_clock_groups`)
- `set_max_delay` without `-datapath_only` on CDC paths
- UVM driver without `seq_item_port.item_done()`

## Skill quick reference

| Topic | Skill |
|---|---|
| FSM design | `fsm-design` |
| CDC, async FIFO | `clock-domain-crossing` |
| SystemVerilog patterns | `systemverilog-coding` |
| SDC/XDC constraints | `timing-constraints` |
| UVM testbench | `uvm-coding` |
| Synthesis-friendly RTL | `synthesis-guidelines` |
| AXI4/Lite/Stream | `axi-protocols` |
| RTL standards | `clean-rtl` |
| Formal verification | `formal-verification` |
| Waveform debug | `waveform-debugging` |
| Xilinx Vivado | `vivado-flow` |
| Intel Quartus | `quartus-flow` |
| Synopsys (DC, VCS, SpyGlass, DFTC, VC Formal) | `synopsys-flow` |
| Cadence (Genus, Xcelium, JasperGold) | `cadence-flow` |
| Low-power design | `low-power-design` |
| DFT (scan, BIST, ATPG) | `dft-patterns` |
| IP reuse | `ip-reuse` |
| Tcl scripting | `tcl-scripting` |
