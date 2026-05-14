# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repo is

`@kishore-damam/vlsi-agkit` is an npm-distributed kit of AI-agent assets (agents, skills, workflows) for VLSI front-end work. **The product is the `.agent/` directory plus a thin Node CLI** that installs/browses it. There is no application runtime — Claude Code/Copilot/Gemini/Cursor/Antigravity load the markdown directly.

When editing this repo you are usually doing one of three things:
1. **Authoring or revising agent/skill/workflow markdown** under `.agent/`.
2. **Changing CLI behavior** in `bin/cli.js` (init flow, list/search/skill/agent/workflow/verify subcommands, frontmatter parser, per-tool generators).
3. **Adjusting verification plumbing** (`Makefile`, `tools.mk`, per-skill `examples/Makefile`).

## Commands

```bash
# CLI (the published binary)
node bin/cli.js <cmd>            # local dev — same as `vlsi-agkit <cmd>` after install
node bin/cli.js init             # interactive installer (writes into cwd)
node bin/cli.js list [skills|agents|workflows]
node bin/cli.js skill <name> [section] | --list
node bin/cli.js agent <name>
node bin/cli.js workflow <name>
node bin/cli.js search <regex>
node bin/cli.js verify [skill]   # delegates to make verify

# Skill verification (compiles/runs SystemVerilog examples)
make help
make list-skills                 # discovered skills (skips _-prefixed dirs)
make verify                      # run every skill's examples/Makefile verify target
make -C .agent/skills/<skill>/examples verify REPO_ROOT=$(pwd)   # one skill

# Simulator selection for verify (see tools.mk):
#   1. iverilog on PATH (default)
#   2. VLSI_SIM env var (e.g. VLSI_SIM=xsim)
#   3. VLSI_SIM_BIN for full path
#   4. .agent/tools.local.mk (gitignored; copy from tools.example.mk)

# Release (maintainers): tag-driven npm publish via .github/workflows/npm-publish.yml
npm version patch && git push && git push --tags
```

There is no test suite (`npm test` is a stub). `make verify` is the closest thing — it exercises the SystemVerilog examples shipped with each skill.

## Architecture

### `.agent/` is the *source* payload (npm-bundled, never copied to user projects)

Everything authoritative lives here. `init` reads from this tree and **generates** per-tool installs at the user's project. The folder is also bundled inside the published npm package so `vlsi-agkit list/skill/...` work via fallback even when no local install exists.

- `.agent/agents/*.md` — 14 specialist personas. Frontmatter `skills:` lists which skills the agent pulls in. The `init` flow expands a chosen role into its skill set via this field. Production-tier agents follow the template: Core Philosophy → Your Mindset → domain Flow → templates → checklists.
- `.agent/skills/<name>/SKILL.md` — 21 index cards (≤300 lines each), with optional `references/` (deep-dive markdown) and `examples/` (compilable SV + Makefile). Eleven are production-grade with deep references (`clean-rtl`, `fsm-design`, `clock-domain-crossing`, `systemverilog-coding`, `sta`, `timing-constraints`, `dft-patterns`, `low-power-design`, `uvm-coding`, `synthesis-guidelines`, `axi-protocols`); the rest are SKILL.md only. Skill dirs prefixed with `_` (`_templates`, `_evals`) are reserved and ignored by both `make` and the CLI. All skills follow the structural template: When-to-use (with Not-for) → Quick reference / Patterns → Anti-patterns → Validation checklist.
- `.agent/workflows/*.md` — 10 slash-command procedures (`/design`, `/verify`, `/sta`, …). Each has a `## Resources` section naming the lead agent, supporting agents, and required/conditional skills, so the workflow file is the entry point that composes the rest of the kit. The Claude Code generator copies these to `.claude/commands/`; Copilot to `.github/prompts/`; etc.

### Per-tool generators (`bin/cli.js`)

`init` runs one **generator function** per selected tool (`installClaude`, `installCopilot`, `installGemini`, `installCursor`, `installAntigravity`). Each generator:

1. Reads source SKILL.md / agent / workflow markdown from `.agent/` in the npm package.
2. Splits the YAML frontmatter via `splitFrontmatter()` and rewrites it via `fmYaml()` to match the target tool's expectations (Claude Code and Copilot cloud-agent skills both want `name:` + `description:`; Cursor wants `description:` + `alwaysApply: false`).
3. Writes the result to the tool's native directory (`.claude/skills/<name>/SKILL.md`, `.github/skills/<name>/SKILL.md` per the [Copilot cloud-agent skills spec](https://docs.github.com/en/copilot/how-tos/copilot-on-github/customize-copilot/customize-cloud-agent/add-skills), `.gemini/skills/`, `.cursor/rules/`, `.agents/skills/`).

Output layout per tool: see README "Supported AI Tools" table. Multiple tools = duplicated content (deliberate — each tool's install is self-contained, no shared `.agent/` indirection).

### CLI shape (`bin/cli.js`)

- `findAgentRoot()` resolves `.agent/` from cwd first, then falls back to the bundled copy inside the npm package — this is what makes `npx vlsi-agkit list` work from any directory, including projects where `init` was never run.
- `readFrontmatter()` and `splitFrontmatter()` are hand-rolled YAML parsers. They must handle CRLF (Windows). Don't reach for a YAML lib; keep them tolerant of `\r\n` and quoted values.
- `fmYaml()` quotes any value containing YAML-significant chars (`* & ! | > % @ : # ` " '`) — handles glob patterns and descriptions with colons.
- `init` is interactive (arrow-key checkbox lists via `prompts`), with **nothing pre-selected by default**. Roles map → skills via agent frontmatter; tool selection drives which generators run. Flags `--tools`, `--roles`, `--skills`, `--yes` make it scriptable.
- Subcommands: `init | list | skill | agent | workflow | search | verify | version | help`.

### Skill verification tiers

Each `examples/Makefile` declares a tier that controls how `make verify` treats it:

| Tier | Behavior |
|---|---|
| `build-sim` | compile + run; self-checking TB reports PASS/FAIL |
| `build-only` | compile-only syntax check |
| `needs-vendor-sim` | skipped on iverilog (UVM, SV interfaces) |
| `tool-output` | XDC/SDC/synthesis reports — not compilable, skipped |
| `manual-review` | reference-only |

When adding a new skill with examples, write the `examples/Makefile` to declare its tier so CI behaves correctly.

## Conventions worth knowing

- **Tool-agnostic content.** When writing skills/agents/workflows, do not assume Claude Code specifically — the same markdown is consumed by Copilot, Gemini, Cursor, and Antigravity.
- **Underscore-prefix = hidden.** Anything under `.agent/skills/_*` is template/tooling and is filtered out by both the Makefile (`filter-out _%`) and the CLI's `listDir` helper. Use this for scaffolding you don't want shipped as a real skill.
- **Frontmatter is the contract.** Roles ↔ skills mapping, skill metadata, and CLI listings all read frontmatter. Keep `name:`, `description:`, and (for agents) `skills:` accurate; mismatches will silently break `init`.
- **No behavior changes via comments.** When fixing the frontmatter parser or CLI flow, prefer extending tests/examples over leaving "// handles CRLF" notes.

## Out-of-scope reminders

- The repo has no lint/test/typecheck pipeline beyond `make verify`. Don't invent one without being asked.
- Don't introduce a build step for the CLI — it ships as plain CommonJS so `npx` works on Node ≥14 with no install.
