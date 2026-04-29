# AGENTS.md — VLSI Front-End Development

This project uses the [VLSI Agent Kit](https://github.com/kishore-damam/vlsi-kit)
at `.agent/`. Specialist agents and skills are plain Markdown that you load on
demand.

## Project type

VLSI front-end development (FPGA & ASIC). RTL is SystemVerilog (preferred),
Verilog-2001, or VHDL-2008. Verification uses UVM, SVA, and coverage.

## Specialist agents (`.agent/agents/`)

14 personas covering:
- **Design:** rtl-designer, fpga-specialist, asic-specialist
- **Verify:** verification-engineer, debugger
- **Implement:** synthesis-engineer, timing-analyst, physical-design-engineer
- **Analysis:** power-analyst, lint-reviewer
- **Process:** orchestrator, project-planner, ip-integrator
- **Docs:** documentation-writer

Each agent's frontmatter lists which skills it relies on (`skills: a, b, c`).

## Skills (`.agent/skills/`)

18 skills, each with:
- `SKILL.md` — the index card (when to use, core patterns, anti-patterns)
- `references/` — deep-dive markdown for specific topics
- `examples/` — compilable worked examples + Makefile

Production-grade skills (full reference + examples):
- `fsm-design`, `clock-domain-crossing`, `systemverilog-coding`
- `timing-constraints`, `uvm-coding`, `synthesis-guidelines`

Other skills:
- `clean-rtl`, `formal-verification`, `waveform-debugging`
- `fpga-flows`, `asic-flows`, `axi-protocols`
- `low-power-design`, `dft-patterns`, `ip-reuse`
- `tcl-scripting`, `brainstorming`, `plan-writing`

## Workflows (`.agent/workflows/`)

End-to-end procedures: `design`, `verify`, `synthesize`, `debug`, `lint`,
`timing`, `review`, `integrate`, `plan`, `brainstorm`.

## Routing

For any task:
1. Pick the matching agent from `.agent/agents/`.
2. Load `SKILL.md` for each skill listed in the agent's frontmatter.
3. Pull deeper context from `references/` only when needed.
4. Use the matching workflow for multi-step procedures.

## Coding standards (always apply)

- New SystemVerilog: `logic` only (no `reg`/`wire`).
- Clocked: `always_ff` with `<=`.
- Combinational: `always_comb` with default assignments.
- UVM: factory-create with `type_id::create`.
- SDC: pair `set_multicycle_path N -setup` with `N-1 -hold`.
