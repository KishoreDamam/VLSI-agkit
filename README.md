# VLSI Agent Kit

> AI Agent templates for VLSI Front-End Development (FPGA & ASIC)

A production-grade collection of skills, agents, and workflows that turn Claude (or any compatible AI coding agent) into a domain-aware VLSI assistant — covering RTL design, verification, synthesis, timing closure, and CDC.

## Quick Install

```bash
npx @kishore-damam/vlsi-agkit init
```

The installer is interactive — arrow-key checkbox lists with **nothing pre-selected**:

1. **Which AI tools** you use (Claude Code, GitHub Copilot, Gemini CLI, Cursor, Google Antigravity)
2. **Which roles** you need (rtl-designer, verification-engineer, timing-analyst, fpga-specialist, …) — skills come bundled per role from each agent's `skills:` frontmatter, so you don't pick individual skills

Selecting `verification-engineer` automatically pulls in `uvm-coding`, `formal-verification`, and `waveform-debugging`. Tool installs (`.claude/`, `.github/`, `GEMINI.md` + `.gemini/`, `.cursor/rules/`, `AGENTS.md` + `.agents/`) are only written for tools you actually select.

### Non-interactive install (CI / scripted)

```bash
# Install EVERYTHING (all 5 tools, all 14 roles, all 21 skills)
npx @kishore-damam/vlsi-agkit init --yes

# Specific tools, all roles
npx @kishore-damam/vlsi-agkit init --tools=claude,copilot --yes

# Specific roles only — no tool configs unless --tools is also given
npx @kishore-damam/vlsi-agkit init --roles=rtl-designer,verification-engineer --yes

# Both tools and roles, scoped
npx @kishore-damam/vlsi-agkit init --tools=cursor --roles=fpga-specialist --yes

# Direct skill selection (advanced — bypasses the role mapping)
npx @kishore-damam/vlsi-agkit init --skills=fsm-design,uvm-coding --yes
```

### Global install

```bash
npm install -g @kishore-damam/vlsi-agkit
vlsi-agkit init
```

### Manual installation

If you don't want to run `init`, you can clone this repo and copy the relevant
per-tool subdirectory (e.g. `.cursor/rules/`) directly. The `.agent/` folder
inside this repo is the source of truth that `init` reads from to generate
each tool's install — you generally shouldn't copy `.agent/` into your project.

## Use the kit without an AI tool (CLI mode)

The `vlsi-agkit` CLI lets you browse, search, and run the kit directly from
your terminal — no AI assistant required. Run any command with `npx` (no
install needed) or after `init`/global install.

```bash
# Browse
npx @kishore-damam/vlsi-agkit list                       # everything
npx @kishore-damam/vlsi-agkit list skills                # only skills
npx @kishore-damam/vlsi-agkit skill clock-domain-crossing
npx @kishore-damam/vlsi-agkit skill timing-constraints --list
npx @kishore-damam/vlsi-agkit skill timing-constraints multicycle-paths

# Search across the whole kit (case-insensitive regex)
npx @kishore-damam/vlsi-agkit search "async FIFO"
npx @kishore-damam/vlsi-agkit search "set_multicycle_path"

# Read agent or workflow definitions
npx @kishore-damam/vlsi-agkit agent rtl-designer
npx @kishore-damam/vlsi-agkit workflow design

# Run example verification (requires iverilog or vendor sim — see below)
npx @kishore-damam/vlsi-agkit verify              # all skills
npx @kishore-damam/vlsi-agkit verify fsm-design   # one skill
```

### Pipe-friendly output

All `skill`, `agent`, and `workflow` commands print raw markdown to stdout, so
you can pipe to a pager or markdown renderer:

```bash
vlsi-agkit skill uvm-coding | less
vlsi-agkit skill fsm-design | glow -          # https://github.com/charmbracelet/glow
vlsi-agkit skill cdc > cdc-cheatsheet.md      # save to file
```

### Source resolution

If you've run `vlsi-agkit init` in your project, the CLI uses the local
`.agent/` folder. Otherwise it falls back to the `.agent/` bundled inside the
npm package — so `npx vlsi-agkit list` works from any directory, even on a
clean machine.

## Supported AI Tools

`init` writes a **self-contained kit at each tool's native location**, with the
right frontmatter for that tool. There is no shared `.agent/` folder in your
project — pick the tools you use and you only see the directories you need.

| Tool | What gets written | Slash commands |
|---|---|---|
| **Claude Code** | `.claude/skills/<name>/SKILL.md`, `.claude/agents/<role>.md`, `.claude/commands/<workflow>.md` | ✅ via `.claude/commands/` |
| **GitHub Copilot** | `.github/copilot-instructions.md` (index) + `.github/skills/<name>/SKILL.md` ([cloud-agent skills spec](https://docs.github.com/en/copilot/how-tos/copilot-on-github/customize-copilot/customize-cloud-agent/add-skills), with `references/`+`examples/`) + `.github/prompts/<workflow>.prompt.md` | ✅ via `/<workflow>` prompts |
| **Gemini CLI** | `GEMINI.md` (router) + `.gemini/{skills,agents,workflows}/<name>.md` | ✅ via GEMINI.md `@file` includes |
| **Cursor** | `.cursor/rules/<skill>.mdc` (and `agent-<role>.mdc`, `workflow-<name>.mdc`) with `description:` + `alwaysApply: false` | ✅ via Cursor's "rule" mechanism |
| **Google Antigravity** | `AGENTS.md` (router) + `.agents/{skills,roles,workflows}/<name>.md` | ✅ via `.agents/workflows/` |

If you select multiple tools, the same skill content is written to each tool's
folder (duplicated by design — no `.agent/` indirection means each tool's
install is fully self-contained and standalone).

### Selecting no tool (CLI-only mode)

If you skip every tool, `init` writes nothing. The `vlsi-agkit` binary still
works because it falls back to the `.agent/` bundled inside the npm package.

## What's Included

| Component     | Count | Description                                                        |
| ------------- | ----- | ------------------------------------------------------------------ |
| **Agents**    | 14    | Specialist AI personas (RTL, Verification, Synthesis, Timing, etc.) |
| **Skills**    | 20    | Domain-specific knowledge modules                                  |
| **Workflows** | 10    | Slash command procedures                                           |

## Skills

Skills are tiered: each has a thin `SKILL.md` index card (≤300 lines) plus deep-dive `references/` and runnable `examples/`.

### Production-grade (Wave 1) ⭐

These ten skills ship with full reference docs, compiled examples, validation gates, and citations:

| Skill | Type | What it covers |
|---|---|---|
| `clean-rtl` | coding | Simulation races (Cummings' 8 NBA rules), sim/synth mismatch (8 causes), latch inference & `unique`/`priority`, sync-reset coding idiom, **FPGA reset strategy (async-assert / sync-deassert)** |
| `fsm-design` | coding | One/two/three-process FSMs, encoding tradeoffs, timeout counters, SVA assertions |
| `clock-domain-crossing` | flow | 2-FF synchronizers, async FIFO with Gray pointers, handshake CDC, false-path vs max-delay |
| `systemverilog-coding` | coding | `logic`/`reg`/`wire`, interfaces+modports, generate, struct drivers, `always_comb`/`_ff` |
| `sta` | flow | **Master-level STA** — slack equations, CRPR, OCV/AOCV/POCV, MMMC corners, SI, useful skew, latch borrow, report_timing deep-dive |
| `timing-constraints` | flow | SDC/XDC: `create_clock`, I/O delays, multicycle paths, **8-category false-paths catalog**, clock characteristics (latency / propagation / sense / ideal), port electrical (`set_driving_cell` / load / fanout), modal analysis (`set_case_analysis`), combinational/feedthrough paths, Xilinx XDC |
| `dft-patterns` | flow | Scan chains (controllability/observability), capture/shift, fault models (stuck-at, transition, cell-aware), ATPG coverage targets |
| `low-power-design` | flow | UPF power domains, isolation/retention, **FPGA clock-control primitives (BUFGCE / BUFGMUX vs logic gating), voltage scaling / DVFS, dual-edge registers, termination & decoupling** |
| `uvm-coding` | coding | UVM 1.2 components, sequences, TLM analysis ports, dual-FIFO scoreboards, RAL |
| `synthesis-guidelines` | flow | Synthesis-friendly RTL, attributes, **retiming / register balancing (with reset-uniformity and synchronizer traps), FSM compilation & encoding**, GLS readiness, X-propagation, congestion-aware RTL |

### Other skills

| Skill | What it covers |
|---|---|
| `formal-verification` | Assertions, properties, model checking |
| `waveform-debugging` | Waveform analysis, debug techniques |
| `vivado-flow` | Xilinx Vivado synthesis, impl, ILA/VIO debug |
| `quartus-flow` | Intel Quartus compile flow, M10K/M20K, DSP inference |
| `synopsys-flow` | DC, VCS, SpyGlass, DFT Compiler, VC Formal |
| `cadence-flow` | Genus, Xcelium, JasperGold |
| `axi-protocols` | AXI4, AXI-Lite, AXI-Stream |
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
| `/sta`         | Static Timing Analysis (closure + signoff) |
| `/review`      | Code review                           |
| `/integrate`   | IP integration                        |

Example:
```
/design AXI4 memory controller
/verify FIFO with UVM
/sta close WNS on path through u_alu/add_*
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

## Release process (maintainers)

Publishing to npm is automated via GitHub Actions. To cut a release:

```bash
# 1. Bump the version in package.json (semver)
npm version patch    # or: minor / major

# 2. Push the commit and the tag
git push && git push --tags
```

The `Publish to npm` workflow (`.github/workflows/npm-publish.yml`) fires on
any tag matching `v*`, verifies the tag matches `package.json`, runs
`npm publish --access public --provenance`, and creates a GitHub Release with
auto-generated notes.

**One-time setup** (already done if you can see published versions):
- Create an npm automation token at https://www.npmjs.com/settings/<user>/tokens
- Add it as repository secret `NPM_TOKEN` in GitHub Settings → Secrets and variables → Actions

## Acknowledgements

This kit is based on the [Antigravity Kit](https://github.com/vudovn/antigravity-kit) by [@vudovn](https://github.com/vudovn).
The structure and agentic patterns were adapted for the VLSI domain.

## License

MIT
