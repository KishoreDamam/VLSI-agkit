# Multi-Role, Multi-Tool VLSI-KIT Installer — Design

**Date:** 2026-04-22
**Status:** Approved (pending spec review)
**Scope:** `vlsi-kit/` package

## Summary

Enhance the VLSI-KIT installer (`vlsi-agkit init`) so a user can:

1. Pick a **role profile** (preset bundle of agents/skills/workflows) instead of always getting all 14 specialist agents.
2. Pick **one or more target tools** (Claude Code, Gemini CLI, VS Code, Antigravity, Cursor, Windsurf) and have the kit emitted in each tool's native layout from a single canonical source.

The current installer copies `.agent/` wholesale and drops a `GEMINI.md` at the root — no role selection, no support for Claude Code's `.claude/`, Cursor's `.cursor/rules/`, Windsurf's `.windsurf/rules/`, or VS Code Copilot's instruction file.

## Goals

- **One source of truth.** Canonical content stays in `.agent/`. Tool-specific layouts are derived at install time via adapters. Content authors edit one tree.
- **Interactive UX.** `npx vlsi-agkit init` prompts for role and tools; CLI flags still supported for automation.
- **Role profiles.** A small, curated set of six profiles covering the common VLSI specializations plus a full-stack default.
- **Isolated adapters.** Each supported tool is a self-contained module with a narrow interface.
- **Safe conflicts.** Never silently overwrite existing files; prompt (interactive) or abort (non-interactive without `--force`).

## Non-Goals (YAGNI)

- User-defined custom profiles via config file.
- `update` / `sync` commands to re-emit on canonical changes.
- Per-agent pick-list overrides on top of a profile.
- MCP server installation, tool-specific deep config beyond basic rule/agent emission.

## Architecture

```
vlsi-kit/
├── bin/
│   ├── cli.js                # Entry point — refactored to orchestrate
│   ├── prompts.js            # Interactive prompts via @inquirer/prompts
│   ├── profiles.js           # Role profile registry
│   ├── fs-util.js            # Shared copy / write / conflict helpers
│   └── adapters/
│       ├── index.js          # Adapter registry: id → module
│       ├── claude.js
│       ├── gemini.js
│       ├── vscode.js
│       ├── antigravity.js
│       ├── cursor.js
│       └── windsurf.js
├── .agent/                   # Canonical source — unchanged
│   ├── agents/
│   ├── skills/
│   ├── workflows/
│   ├── rules/
│   └── ARCHITECTURE.md
└── package.json              # + @inquirer/prompts, engines bumped to >=18
```

### Data flow

```
User input
   │
   ▼
┌──────────────┐   ┌──────────────┐   ┌──────────────────┐
│  prompts.js  │──▶│  profiles.js │──▶│  Resolved        │
│ (or flags)   │   │  .resolve()  │   │  profile object  │
└──────────────┘   └──────────────┘   └────────┬─────────┘
                                               │
                                               ▼
                                      ┌──────────────────┐
                                      │ For each chosen  │
                                      │ tool adapter:    │
                                      │   emit(profile,  │
                                      │        source,   │
                                      │        target)   │
                                      └──────────────────┘
```

## Components

### 1. `bin/profiles.js`

Declarative registry. Profile shape:

```js
{
  id: 'fpga-engineer',
  name: 'FPGA Engineer',
  description: 'FPGA design, Vivado/Quartus flows, timing closure',
  agents: ['fpga-specialist', 'rtl-designer', 'timing-analyst',
           'ip-integrator', 'debugger', 'lint-reviewer'],
  skills:   [/* derived from agent frontmatter + profile extras */],
  workflows:[/* workflow ids to include */]
}
```

**Profiles shipped in v1:**

| id | Agents |
|---|---|
| `full-stack` (default) | all 14 |
| `fpga-engineer` | fpga-specialist, rtl-designer, timing-analyst, ip-integrator, debugger, lint-reviewer |
| `asic-engineer` | asic-specialist, rtl-designer, physical-design-engineer, timing-analyst, power-analyst, debugger, lint-reviewer |
| `verification-engineer` | verification-engineer, debugger, lint-reviewer, documentation-writer |
| `rtl-designer` | rtl-designer, lint-reviewer, documentation-writer |
| `physical-design` | physical-design-engineer, timing-analyst, power-analyst, asic-specialist |

Each profile object carries an explicit `alwaysInclude: ['orchestrator', 'project-planner']` field (module-level constant by default, overridable per profile) rather than a hidden rule inside `resolve()` — keeps the data declarative and lets a future profile opt out.

The `resolve(id)` function returns a full profile object with:
- `agents`: the profile's agents + `alwaysInclude`
- `skills`: expanded by reading each included agent's frontmatter `skills:` field (comma-separated list), unioned with any profile-level `skills:` additions, deduplicated
- `workflows`: the profile's workflow ids

**Edge case:** `full-stack` is a sentinel — no filtering, passes through everything.

### 2. `bin/prompts.js`

Prompts using `@inquirer/prompts`, asked in this order:

1. `select` — role profile (list)
2. `checkbox` — tools (multi-select, at least one required)
3. `input` — target directory (default `.`)
4. `confirm` — per-conflict overwrite (only fired later, in `cli.js`, if any target path exists and `--force` was not passed)

When `process.stdin.isTTY === false` or any of `--role`/`--tools` flags are present, prompts are skipped and CLI args are used instead. Missing flags in non-interactive mode → error with guidance.

### 3. `bin/adapters/<tool>.js`

Each adapter exports:

```js
module.exports = {
  id: 'cursor',
  name: 'Cursor',
  targetPaths: ['.cursor/'],            // declared up front for conflict pre-check
  emit({ profile, sourceDir, targetDir, log, force }) {
    // Read canonical files, transform, write to targetDir
  }
}
```

**Per-adapter responsibility:**

| Adapter | Reads from `.agent/` | Writes |
|---|---|---|
| `claude` | agents/, workflows/, skills/, rules/, package `CLAUDE.md` | `.claude/agents/*.md` (filtered), `.claude/commands/*.md` (workflows), `CLAUDE.md` at target root (see note A) |
| `gemini` | rules/GEMINI.md | `GEMINI.md` at target root (filtered to profile agents) |
| `antigravity` | everything | `.agent/` (filtered to profile) — current behavior |
| `cursor` | agents/, skills/ | `.cursor/rules/*.mdc` with frontmatter `{description, globs, alwaysApply}` (globs map — see note B) |
| `windsurf` | agents/, skills/ | `.windsurf/rules/*.md` (reuses the globs map from cursor, emitted as frontmatter) |
| `vscode` | package `CLAUDE.md`, profile | `.github/copilot-instructions.md` (see note A) |

**Note A — `CLAUDE.md` sourcing for `claude` and `vscode` adapters.** The canonical `CLAUDE.md` lives at the package root (`vlsi-kit/CLAUDE.md` — the kit's own configuration file shipped in the npm package), not inside `.agent/`. Both adapters read this file and **filter its Agent Routing table** to include only rows whose agent appears in the resolved profile. For `full-stack`, no rows are removed. The VS Code adapter additionally strips the `## Available Slash Commands` section (Copilot has no slash command notion) and renames the heading to match Copilot conventions.

**Note B — Cursor/Windsurf globs map.** Hardcoded in `adapters/globs.js` (shared module):

| Agent id | `globs` |
|---|---|
| `rtl-designer`, `ip-integrator` | `**/*.{sv,svh,v,vh,vhd,vhdl}` |
| `verification-engineer` | `**/{tb,test,tests,sim}/**/*.{sv,svh,v}`, `**/*_tb.{sv,v}` |
| `synthesis-engineer` | `**/*.{tcl,sdc}`, `**/synth/**` |
| `timing-analyst` | `**/*.{sdc,xdc,tcl}` |
| `fpga-specialist` | `**/*.{xdc,qsf,xpr}`, `**/fpga/**` |
| `asic-specialist`, `physical-design-engineer` | `**/*.{lef,def,lib,sdc}`, `**/pnr/**`, `**/synth/**` |
| `power-analyst` | `**/*.upf`, `**/power/**` |
| `debugger`, `lint-reviewer`, `documentation-writer`, `project-planner`, `orchestrator` | `alwaysApply: true` (no glob restriction) |

**Transformation rules (Cursor MDC example):**

Input `.agent/agents/rtl-designer.md` frontmatter:
```yaml
---
name: rtl-designer
description: Expert in RTL design...
skills: clean-rtl, systemverilog-patterns, fsm-design, axi-protocols
---
```

Output `.cursor/rules/rtl-designer.mdc`:
```yaml
---
description: Expert in RTL design... Triggers on design, module, implement, FSM.
globs: "**/*.{sv,svh,v,vh,vhd,vhdl}"
alwaysApply: false
---
# RTL Designer ... (body unchanged)
```

`globs` is adapter-specific and derived from a hardcoded map per agent category in the adapter.

### 4. `bin/cli.js`

Orchestrator. Flow:

1. Parse flags.
2. If interactive and flags missing → run prompts.
3. `profiles.resolve(roleId)` → profile object.
4. For each selected tool, call `adapter.targetPaths` → collect conflicts.
5. If conflicts: prompt (interactive) / `--force` respected / abort otherwise.
6. For each selected adapter: `adapter.emit({ profile, sourceDir, targetDir, ... })`.
7. Print summary: profile name, counts (agents/skills/workflows), tools written, paths.

### 5. `bin/fs-util.js`

Shared helpers: `copyDir`, `copyFile`, `writeFile`, `pathExists`, `readFrontmatter`. Kept tiny — no templating engine.

The `readFrontmatter` parser handles **only the subset used by canonical agent/skill files**: flat key-value pairs between `---` fences, string scalars, and comma-separated lists on a single line (e.g., `skills: clean-rtl, systemverilog-patterns`). Nested mappings, block scalars, multi-line lists, anchors, and quoted escapes are **not supported** and will throw. This is intentional — if canonical content ever needs richer YAML, swap in `js-yaml` at that point rather than extending the regex parser.

## CLI contract

```
vlsi-agkit init [options]

Options:
  --role <id>          Profile id (skips prompt)
  --tools <csv>        Comma-separated tool ids (skips prompt)
                       Valid: claude,gemini,vscode,antigravity,cursor,windsurf
  --dir <path>         Target directory (default: .)
  --force              Overwrite existing target paths
  --list-profiles      Print profiles and exit
  --list-tools         Print tools and exit

Examples:
  vlsi-agkit init
  vlsi-agkit init --role fpga-engineer --tools claude,cursor
  vlsi-agkit init --role full-stack --tools antigravity --dir ./my-project
```

`help` / `version` commands unchanged.

## Error handling

| Condition | Behavior |
|---|---|
| Unknown `--role` | Exit 1, print list of valid ids |
| Unknown tool in `--tools` | Exit 1, print list of valid ids |
| No tools selected (empty checkbox) | Prompt again (min 1 required) |
| Target path exists, not interactive, no `--force` | Exit 1, list conflicting paths |
| Target path exists, interactive | Per-path confirm; Ctrl-C aborts cleanly |
| Source canonical file missing | Exit 1, print canonical source path — indicates broken npm package |
| Target dir not writable | Exit 1 with OS error |

## Testing strategy

- **Runner:** `node:test` (built-in — no dep added).
- **Unit:**
  - `profiles.resolve()` for every profile id (including unknown).
  - **Skill-expansion logic** inside `resolve()`: given a fixture agent set where agent A declares `skills: x, y` and agent B declares `skills: y, z`, assert the resolved skill set is `{x, y, z}` (deduplicated). Cover an agent with empty `skills:` field and an agent whose declared skill isn't present on disk (should warn, not crash).
  - Each adapter's `emit()` against a fixture mini-`.agent/` tree — snapshot comparison of output file tree + key file contents.
  - `CLAUDE.md` Agent Routing table filtering (claude + vscode adapters) against a non-`full-stack` profile.
  - Frontmatter parser edge cases, including the unsupported cases that must throw.
- **Integration:**
  - Run `init` against `fs.mkdtempSync(os.tmpdir())` for each (profile × tool) combo; assert target files exist, conflict detection fires when pre-seeded.
  - Non-interactive flag path with missing required flag → exit 1.
- **Manual smoke:** `npm link`, run `vlsi-agkit init` in an empty dir, verify each tool's output opens correctly in its IDE.

## Migration / compatibility

- Default behavior when run with **no flags and interactive TTY**: prompt. This is a UX change but not a silent regression (user sees prompts).
- Default behavior when run with **no flags in non-interactive mode**: error with guidance. The previous implicit "install everything" is intentionally removed to prevent surprise writes.
- Existing users relying on `vlsi-agkit init` in CI should migrate to `--role full-stack --tools antigravity` (the closest equivalent to current behavior).
- README updated to document the migration.

## Dependencies

- **Added:** `@inquirer/prompts` (MIT, ~30 KB, zero runtime deps beyond Node built-ins).
- `engines.node` bumped from `>=14.0.0` to `>=18.0.0` (required by `@inquirer/prompts`).

## Open questions (for reviewer)

None — all scope decisions resolved during brainstorming.

## References

- Current CLI: `bin/cli.js`
- Canonical content: `.agent/`
- Existing agent frontmatter convention: `.agent/agents/*.md`
- Tool docs consulted: Cursor MDC rules, Windsurf rules, Claude Code agents/commands, VS Code Copilot custom instructions
