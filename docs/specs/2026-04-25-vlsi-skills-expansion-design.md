# VLSI Skills Expansion — Design Spec

**Date:** 2026-04-25
**Owner:** Kishore Damam
**Status:** Draft pending review

---

## 1. Goal

Expand the existing 18 thin VLSI skills under `.agent/skills/` into 27 production-grade
professional skills, suitable for shipping in the `@kishore-damam/vlsi-agkit` npm package.
Each skill must be deep enough that a working FPGA/ASIC engineer can rely on it without
external references for the patterns and procedures it covers, while staying token-efficient
through tiered progressive disclosure.

## 2. Non-goals

- Touching the 14 agents under `.agent/agents/` (only renames force reference updates).
- Touching the 10 workflows under `.agent/workflows/` (only renames force reference updates).
- Modifying the npm packaging logic.
- Building skills for back-end (PnR, place-and-route specifics) beyond what
  `physical-design`-adjacent flow skills already cover.
- Introducing vendor-locked content. Skills stay vendor-neutral; vendor-specific
  callouts are inline notes only.

## 3. Decisions log

| # | Decision | Rationale |
|---|---|---|
| 1 | Tiered structure: SKILL.md + `references/` + `examples/` | Balances depth and token cost. |
| 2 | Wave 1 core (6) full-depth first, then Wave 2 (21) breadth | Templates emerge from pilots; gates control drift. |
| 3 | Wave 1 core: `fsm-design`, `clock-domain-crossing`, `systemverilog-coding`, `timing-constraints`, `uvm-coding`, `synthesis-guidelines` | High-leverage, high-risk-if-wrong, broad usage. |
| 4 | Add 9 new skills | Fill gaps in front-end coverage (assertions, coverage, reset, UPF, FIFOs, arbitration, sim-flows, handshake, microarchitecture). |
| 5 | Vendor-neutral primary content with inline vendor callouts | Portable across Synopsys, Cadence, Xilinx, Intel. |
| 6 | Citations: hybrid — cite IEEE/AMBA when stating normative rules; skip for general practice | Trust without bloat. |
| 7 | Validation: worked-example cross-check (each skill has buildable `examples/`) | Ensures skill content actually works. |
| 8 | Keep `brainstorming` and `plan-writing` as VLSI-flavored skills (no "superpowers" branding) | Distinct VLSI value (PPA tradeoffs, signoff gates). |
| 9 | Two templates: **coding-skill** vs **flow-skill** | One template misfits the other type. |
| 10 | Renames: `systemverilog-patterns` → `systemverilog-coding`; `uvm-patterns` → `uvm-coding`; `dft-patterns` → `dft-strategy` | "Patterns" was unclear; new names match content. |
| 11 | Validation backend: simulator discovered via PATH or env, never hardcoded | Kit ships to many users, paths differ. |
| 12 | Skill-creator baseline-eval: Wave 1 only | Quantitative before/after for the highest-leverage skills only; full eval matrix not worth it for Wave 2. |

## 4. Scope

### 4.1 All 27 skills

**Coding skills (8)** — code-construct reference with anti-patterns:
`systemverilog-coding`, `fsm-design`, `fifo-design`, `arbitration`, `sva-assertions`,
`axi-protocols`, `handshake-protocols`, `uvm-coding`.

**Flow skills (19)** — numbered procedures with decision flowcharts and validation gates:
`clock-domain-crossing`, `reset-strategy`, `timing-constraints`, `synthesis-guidelines`,
`formal-verification`, `functional-coverage`, `dft-strategy`, `asic-flows`, `fpga-flows`,
`low-power-design`, `power-intent-upf`, `rtl-microarchitecture`, `clean-rtl`, `ip-reuse`,
`waveform-debugging`, `simulation-flows`, `tcl-scripting`, `brainstorming`, `plan-writing`.

### 4.2 Wave 1 core (6, full depth, sequential, gated)

Order:
1. `fsm-design` — coding-skill template pilot
2. `clock-domain-crossing` — flow-skill template pilot
3. `systemverilog-coding`
4. `timing-constraints`
5. `uvm-coding`
6. `synthesis-guidelines`

### 4.3 Wave 2 batches (21, parallel within batch)

- **Batch A (coding):** `fifo-design`, `arbitration`, `handshake-protocols`,
  `axi-protocols`, `sva-assertions`
- **Batch B (flow-RTL):** `reset-strategy`, `clean-rtl`, `ip-reuse`,
  `rtl-microarchitecture`
- **Batch C (flow-tool):** `formal-verification`, `functional-coverage`,
  `simulation-flows`, `tcl-scripting`, `waveform-debugging`
- **Batch D (flow-impl):** `dft-strategy`, `asic-flows`, `fpga-flows`,
  `low-power-design`, `power-intent-upf`, `brainstorming`, `plan-writing`

## 5. Skill anatomy

Every skill is a directory:

```
.agent/skills/<skill-name>/
├── SKILL.md              # frontmatter + concise primary content (≤ ~400 lines)
├── references/           # deep-dive content, loaded only when needed
│   ├── <topic-N>.md
│   └── vendor-notes.md   # vendor-specific deviations
└── examples/             # worked-example validation artifact
    ├── <name>.sv
    ├── tb_<name>.sv
    └── Makefile          # builds with simulator chosen at runtime
```

**Frontmatter:**
```yaml
---
name: <skill-name>
description: <one-line trigger description>
type: coding | flow
---
```

**SKILL.md content rules:**
- ≤400 lines. Anything deeper → `references/<topic>.md`.
- Vendor-callouts inline as labeled notes (`Vivado:`, `DC:`, `Genus:`, `VCS:`, `Questa:`,
  `Verilator:`).
- Citations only when stating a normative rule — IEEE 1800-2017 (SystemVerilog),
  IEEE 1801 (UPF), ARM AMBA AXI4 spec, vendor user-guide section references.

## 6. Templates

### 6.1 Coding-skill template

```markdown
---
name: <skill-name>
description: <one-liner>
type: coding
---

# <Skill Title>

> <one-line scope statement>

## When to use
- triggering situations

## Quick reference
| Pattern | Use when | Anti-pattern |

## Core patterns
### <Pattern N>
- **Use when:** ...
- **Code:** canonical snippet (≤25 lines). Variants in references/<topic>.md
- **Gotchas:** ...

## Anti-patterns (do NOT do this)
- numbered list with brief why

## Validation checklist (before declaring code "done")
- [ ] item

## See also
- references/<topic>.md
- examples/<name>.sv
```

### 6.2 Flow-skill template

```markdown
---
name: <skill-name>
description: <one-liner>
type: flow
---

# <Skill Title>

## When to use
## Pre-requisites
## Procedure
1. Step — what + why + how to verify
   - Vendor-callout if applicable
2. Step ...

## Decision flowchart (graphviz dot block)

## Validation gates
- Gate N: condition

## Common failure modes & recovery
| Symptom | Likely cause | Fix |

## Citations (only normative rules)
- IEEE 1800-2017 §X.Y: "..."

## See also
- references/<vendor>.md
- examples/<name>/
```

### 6.3 Templates are committed

Both templates live at `.agent/skills/_templates/` so future skills have a starting
point. Reviewer subagents check conformance against these files.

## 7. Validation strategy

### 7.1 Worked-example tiers

Each `examples/Makefile` declares one of these targets as default:

| Tier | What runs | Target skill set |
|---|---|---|
| **build+sim** | compile + elaborate + run self-checking testbench | most coding skills |
| **build only** | compile + elaborate, no run | SVA-heavy, library-heavy |
| **tool-output** | run a `.sdc`/`.upf`/Tcl script and diff against an expected log | flow skills with tool artifacts |
| **manual-review** | no automated check; human reviewer per `agents/grader.md` rubric | rare; only when nothing else fits |

### 7.2 Tool discovery (no hardcoded paths)

Precedence:
1. **PATH** — Makefiles invoke `xvlog`, `xelab`, `xsim`, `iverilog`, `vcs`, `xrun`,
   `vsim` by bare name. Standard EDA practice (`source settings64.sh` or vendor
   equivalent before running).
2. **Env vars** — `VLSI_SIM` selects the simulator (e.g., `xsim`, `iverilog`, `vcs`,
   `xrun`, `vsim`). `VLSI_SIM_BIN` overrides the bin directory.
3. **Per-user opt-in config** — `.agent/tools.local.mk` is **gitignored**, included
   by Makefiles via `-include`. A committed `tools.example.mk` documents the
   convention.

**First-run UX** when nothing is found:

```
ERROR: no SystemVerilog simulator found on PATH.
Expected one of: xsim, iverilog, vcs, xrun, vsim.
Either add the simulator to PATH (typical: `source <vendor>/settings64.sh`)
or set VLSI_SIM_BIN in .agent/tools.local.mk (see tools.example.mk).
```

### 7.3 CI hook

Root `Makefile` walks `.agent/skills/*/examples/` and runs each `Makefile` target.
A skill whose example fails its tier blocks the PR. Skipping is allowed only when
the skill's `Makefile` declares `tier := manual-review` with a reason.

### 7.4 Skill-creator eval (Wave 1 only)

Before rewriting each Wave 1 skill:
- Snapshot current SKILL.md to `<workspace>/skill-snapshot/`.
- Author 5–8 eval prompts in `<skill>-workspace/iteration-1/evals.json` covering
  realistic user asks for that skill area.
- Run `python -m scripts.run_loop --skill-path <snapshot> --eval-set evals.json`
  to capture baseline pass-rate, time, tokens.
- After rewrite, re-run against the new SKILL.md → `iteration-2/`.
- Aggregate via `scripts.aggregate_benchmark`. Reviewer reads
  `benchmark.md` and the analyst pass.

This produces a quantitative before/after for the six core skills. Wave 2 skills
get reviewer-gate validation only (qualitative).

## 8. Sequencing & gates

### 8.1 Wave 0 — Foundation

Deliverables:
- Both template files in `.agent/skills/_templates/`.
- Root `Makefile` walker + `tools.mk` with PATH/env discovery.
- `tools.example.mk` committed; `.agent/tools.local.mk` added to `.gitignore`.
- Skill-creator eval harness wired up.
- Baseline eval run for the six Wave 1 skills (current versions).

### 8.2 Wave 1 — Core 6 (sequential)

Order:
1. `fsm-design` (coding pilot)
2. `clock-domain-crossing` (flow pilot)
3. `systemverilog-coding`
4. `timing-constraints`
5. `uvm-coding`
6. `synthesis-guidelines`

**Per-skill gate (must pass before next skill starts):**
- Template-conformance check (reviewer subagent vs `_templates/`)
- `examples/` Makefile passes its declared tier
- All `references/<topic>.md` files referenced from SKILL.md exist
- Skill-creator re-eval shows non-regression (pass-rate ≥ baseline)
- Reviewer subagent approves with no Issues

### 8.3 Wave 2 — Breadth (21 skills, 4 parallel batches)

Within a batch: dispatch parallel via Agent tool (one subagent per skill).
Between batches: reviewer gate on the whole batch; fix template drift before
next batch starts.

**Per-batch gate:**
- All skills in the batch pass per-skill gate (minus skill-creator re-eval)
- No template drift across the batch (reviewer reads them as a set)

## 9. Repository layout & migration

### 9.1 New layout

```
.agent/skills/
├── _templates/
│   ├── coding-skill-template.md
│   └── flow-skill-template.md
├── README.md                        # index of all 27 skills, grouped by type
├── <skill-name>/
│   ├── SKILL.md
│   ├── references/
│   └── examples/
└── ... (27 total)

.agent/tools.example.mk              # committed
.agent/tools.local.mk                # gitignored
docs/specs/                          # spec lives here
```

### 9.2 Migration steps

1. Create `_templates/` and commit both templates.
2. For each existing skill: convert single-file `SKILL.md` → directory with the new
   shape. Refactor existing content into the new template, do not discard.
3. Apply renames:
   - `systemverilog-patterns` → `systemverilog-coding`
   - `uvm-patterns` → `uvm-coding`
   - `dft-patterns` → `dft-strategy`
4. Update any cross-references in `.agent/agents/*.md` and `README.md`.
5. Create the 9 new skills with full layout from day one.
6. Update `README.md` skill count (18 → 27).

### 9.3 Out of scope (explicit)

- `.agent/agents/*` and `.agent/workflows/*` are touched only when renames force
  reference updates.
- npm packaging (`bin/`, `package.json` scripts) is unchanged.

## 10. Risks & mitigations

| Risk | Mitigation |
|---|---|
| Template drift across 27 skills | Reviewer-subagent gate after every skill in Wave 1; per-batch reviewer gate in Wave 2 |
| Vendor-callouts go stale | Keep them brief, version-tagged where it matters (`Vivado 2024.1+:`); collect them in `references/vendor-notes.md` for easy audit |
| Examples become unbuildable as tools evolve | CI hook catches it; Wave 0 deliverable |
| User has no simulator | Tool-output / manual-review tiers; first-run UX error gives clear remedy |
| UVM examples too heavy for non-vendor users | UVM skill examples ship with both an xsim Makefile target and a "manual-review" fallback explanation |
| Token cost in actively-loaded SKILL.md | 400-line cap enforced by reviewer; everything deeper goes to `references/` |

## 11. Acceptance criteria

- [ ] All 27 skills follow their template; reviewer subagent says so.
- [ ] Every skill has at least one buildable `examples/` artifact (or a justified
      `manual-review` declaration).
- [ ] Root `make verify` walks all skills and exits 0.
- [ ] Wave 1 core skills show non-regressing skill-creator eval scores.
- [ ] `.agent/skills/README.md` lists all 27 skills with one-line descriptions.
- [ ] No committed file references a system-specific path.
- [ ] `README.md` skill count is updated.

## 12. Next step

After this spec is approved, invoke the `writing-plans` skill to produce the
detailed implementation plan (sized into reviewable PR-sized milestones aligned
to Wave 0 / Wave 1 / Wave 2 structure).
