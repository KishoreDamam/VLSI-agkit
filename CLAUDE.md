# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repo is

`@kishore-damam/vlsi-agkit` is an npm-distributed kit of AI-agent assets (agents, skills, workflows) for VLSI front-end work. **The product is the `.agent/` directory plus a thin Node CLI** that installs/browses it. There is no application runtime — Claude Code/Copilot/Gemini/Cursor/Antigravity load the markdown directly.

When editing this repo you are usually doing one of three things:
1. **Authoring or revising agent/skill/workflow markdown** under `.agent/`.
2. **Changing CLI behavior** in `bin/cli.js` (init flow, list/search/skill/agent/workflow/verify subcommands, frontmatter parser, tool-config writers).
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

### `.agent/` is the payload

Everything user-facing lives here. The CLI and all 5 supported AI tools point at this tree rather than duplicating content, so a skill edit propagates everywhere.

- `.agent/agents/*.md` — 14 specialist personas. Frontmatter `skills:` lists which skills the agent pulls in. The `init` flow expands a chosen role into its skill set via this field.
- `.agent/skills/<name>/SKILL.md` — index card (≤300 lines), with optional `references/` (deep-dive markdown) and `examples/` (compilable SV + Makefile). Skill dirs prefixed with `_` (`_templates`, `_evals`) are reserved and ignored by both `make` and the CLI.
- `.agent/workflows/*.md` — slash-command procedures (`/design`, `/verify`, `/timing`, …). Claude Code surfaces these via `.claude/commands/`.
- `.agent/rules/{AGENTS,GEMINI,copilot-instructions,cursorrules}.md` — templates the `init` command writes into the user's project root for non-Claude tools.

### CLI shape (`bin/cli.js`, single file, ~630 lines)

- `findAgentRoot()` resolves `.agent/` from cwd first, then falls back to the bundled copy inside the npm package — this is what makes `npx vlsi-agkit list` work from any directory.
- `readFrontmatter()` is a hand-rolled YAML-frontmatter parser. It must handle CRLF (Windows) — the most recent breaking commit (`7dbc200`) was a fix here. Don't reach for a YAML lib; keep the parser tolerant of `\r\n` and quoted values.
- `init` is interactive (arrow-key checkbox lists via `prompts`), with **nothing pre-selected by default**. Roles map → skills via agent frontmatter; tool selection drives which config files get written. Flags `--tools`, `--roles`, `--skills`, `--yes` make it scriptable.
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
