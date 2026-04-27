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

Batches are sized to keep parallel dispatch reviewable (≤5 skills per batch).
`brainstorming` and `plan-writing` are process skills, not implementation flows,
so they form their own batch.

- **Batch A (coding, 5):** `fifo-design`, `arbitration`, `handshake-protocols`,
  `axi-protocols`, `sva-assertions`
- **Batch B (flow-RTL, 4):** `reset-strategy`, `clean-rtl`, `ip-reuse`,
  `rtl-microarchitecture`
- **Batch C (flow-tool, 5):** `formal-verification`, `functional-coverage`,
  `simulation-flows`, `tcl-scripting`, `waveform-debugging`
- **Batch D (flow-impl, 5):** `dft-strategy`, `asic-flows`, `fpga-flows`,
  `low-power-design`, `power-intent-upf`
- **Batch E (process, 2):** `brainstorming`, `plan-writing`

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

**What "normative rule" means (cite vs. skip examples):**

| Statement | Cite? | Why |
|---|---|---|
| "VALID must not depend on READY in AXI handshakes" | ✅ Cite — ARM IHI 0022 §A3.3.1 | Protocol-mandated rule; misciting is a bug-class |
| "Use non-blocking assignments in clocked `always_ff` blocks" | ✅ Cite — IEEE 1800-2017 §10.4.2 | Language-mandated semantics; subtle if reader is unsure |
| "Two-flop synchronizers reduce metastability" | ❌ Skip | General practice; widely known, no spec mandates 2 vs 3 |
| "Register output paths for better timing" | ❌ Skip | Heuristic, not a rule |
| "Reset must be released synchronously to its destination clock" | ✅ Cite — IEEE 1800-2017 §4.10 (timing) plus a vendor UG when discussing CDC tooling | Behavior is normative; tooling is vendor-specific |

Default when unsure: skip the citation but link to the relevant `references/`
file. Citation churn is worse than missing citations.

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

**Loader-skip convention:** any directory under `.agent/skills/` whose name begins
with `_` (underscore) is treated as non-skill metadata and ignored by skill
loaders, the root `Makefile` walker, and the skills index. The `_templates/`
directory is the canonical user of this convention; documented in
`.agent/skills/README.md`.

## 7. Validation strategy

### 7.1 Worked-example tiers

Each `examples/Makefile` declares one of these tier tokens (hyphenated to
avoid GNU Make whitespace foot-guns — token is matched exactly via
`ifeq ($(tier),...)`):

| Tier | What runs | Target skill set |
|---|---|---|
| **build-sim** | compile + elaborate + run self-checking testbench | most coding skills |
| **build-only** | compile + elaborate, no run | SVA-heavy, library-heavy |
| **tool-output** | run a `.sdc`/`.upf`/Tcl script and diff against an expected log | flow skills with tool artifacts |
| **needs-vendor-sim** | skip on `iverilog`-only CI; manual diff against committed expected log | UVM-heavy, vendor-only constructs |
| **manual-review** | no automated check; human reviewer per `agents/grader.md` rubric | rare; only when nothing else fits |

### 7.2 Platform support

Validation must run on **Linux**, **macOS**, and **Windows (via Git-Bash or WSL)**.
`examples/Makefile` files are written in POSIX-compatible Make:
- Forward slashes in paths.
- No bashisms in recipes (use `sh`-portable constructs).
- Vendor invocation via bare command name (`xvlog`, `xelab`, `xsim`, etc.) — the
  Windows-side tools provide both `<tool>` and `<tool>.bat`; both work from
  Git-Bash with PATH set.
- Where a recipe genuinely needs a shell, declare `SHELL := /bin/sh` at the top
  of `tools.mk`.

Native Windows `cmd.exe` / PowerShell users are expected to run inside Git-Bash
or WSL. This is documented in `.agent/skills/README.md`.

### 7.3 Tool discovery (no hardcoded paths)

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

### 7.4 CI hook

A `.github/workflows/skills-verify.yml` GitHub Actions workflow runs the root
`Makefile` walker on every PR. The workflow:
- Runs on `ubuntu-latest` and `windows-latest`.
- Installs `iverilog` (apt / chocolatey) — the **license-free baseline tier**.
- Skips skills whose `examples/Makefile` declares `tier := needs-vendor-sim`
  (UVM-heavy, vendor-only constructs); those tier as `manual-review` in CI.
- Fails the PR if any non-skipped skill's example fails.

**Vendor licensing:** the kit assumes contributors **do not** have Vivado/VCS/
Questa licenses. Skills whose worked examples require a vendor sim must either
provide an `iverilog`-compatible reduced example or declare
`tier := needs-vendor-sim` and ship an expected-output log committed alongside
the example so a contributor can do a manual diff. A vendor-sim opt-in CI
workflow can be added later but is **out of scope for this expansion**.

### 7.5 Skill-creator eval (Wave 1 only)

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
- Root `Makefile` walker + `tools.mk` with PATH/env discovery (per §7.3).
- `tools.example.mk` committed; `.agent/tools.local.mk` added to `.gitignore`.
- `.github/workflows/skills-verify.yml` (per §7.4) running on `ubuntu-latest`
  and `windows-latest` with `iverilog` installed.
- Loader-skip rule (`_`-prefixed dirs) implemented and documented (per §6.3).
- Skill-creator eval harness committed under `.agent/skills/_evals/` —
  reproducible by anyone, not a one-shot run.
- Baseline eval run for the six Wave 1 skills (current versions); results
  committed to `.agent/skills/<name>-workspace/iteration-1/`.

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

### 8.3 Wave 2 — Breadth (21 skills, 5 parallel batches A–E)

Batches A–E are defined in §4.3. Within a batch: dispatch parallel via Agent tool
(one subagent per skill). Between batches: reviewer gate on the whole batch; fix
template drift before next batch starts.

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
.github/workflows/skills-verify.yml  # CI hook (§7.4)
docs/specs/                          # spec lives here; excluded from npm tarball
```

**npm tarball scope:** `docs/`, `.github/`, `evals/` workspaces, and any
`*-workspace/` directories are excluded via `.npmignore`. Only `.agent/`,
`bin/`, `package.json`, `README.md`, and `LICENSE` ship to consumers. Keeps
the install lean and prevents shipping reviewer/eval artifacts.

### 9.2 Migration steps

1. Create `_templates/` and commit both templates.
2. For each existing skill: convert single-file `SKILL.md` → directory with the new
   shape. Refactor existing content into the new template; **do not discard**
   correct content.
   - **Correctness exception:** if migration uncovers a technical error in
     existing content (a broken pattern, a wrong claim, a stale vendor command),
     **correct it** and call it out in the commit message under a
     `Fixes existing content:` line. Do not silently propagate broken patterns
     into production-grade skills.
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
| Examples become unbuildable as tools evolve | CI hook (§7.4) catches it; Wave 0 deliverable |
| User has no simulator | Manual-review tier; first-run UX error gives clear remedy |
| UVM examples too heavy for license-free CI | UVM skill examples declare `tier := needs-vendor-sim`; ship expected-output log for manual diff (§7.4) |
| Windows/Linux Makefile portability | POSIX-only Make; CI matrix covers `ubuntu-latest` + `windows-latest` (Git-Bash) (§7.2) |
| Vendor licensing barrier for contributors | Default CI runs license-free `iverilog` only; vendor-sim CI is opt-in and out of scope for this expansion (§7.4) |
| Existing skill content has technical errors | Migration step 2 mandates correction with commit-message call-out; reviewer subagent is briefed to flag broken patterns inherited from old content |
| Token cost in actively-loaded SKILL.md | 400-line cap enforced by reviewer; everything deeper goes to `references/` |
| `_templates/` accidentally loaded as a skill | Loader-skip rule (§6.3): underscore-prefixed dirs ignored |
| Eval workspaces bloat the npm tarball | `.npmignore` excludes `*-workspace/`, `docs/`, `.github/` (§9.1) |

## 11. Acceptance criteria

- [ ] All 27 skills follow their template; reviewer subagent says so.
- [ ] Every skill has at least one `examples/` artifact with a declared tier
      (`build-sim`, `build-only`, `tool-output`, `needs-vendor-sim`, or
      `manual-review`).
- [ ] Root `make verify` walks all skills and exits 0 on a stock
      `iverilog`-only environment (license-free contributor baseline).
- [ ] `.github/workflows/skills-verify.yml` passes on `ubuntu-latest` and
      `windows-latest`.
- [ ] Wave 1 core skills show non-regressing skill-creator eval scores
      vs. their committed `iteration-1/` baselines.
- [ ] Skill-creator eval harness is committed (`.agent/skills/_evals/`) and
      reproducible — `python -m scripts.run_loop ...` works for any
      contributor.
- [ ] `.agent/skills/README.md` lists all 27 skills with one-line descriptions.
- [ ] `.npmignore` excludes spec/CI/workspace dirs from the published tarball.
- [ ] No committed file references a system-specific path.
- [ ] `README.md` skill count is updated (18 → 27).

## 12. Next step

After this spec is approved, invoke the `writing-plans` skill to produce the
detailed implementation plan (sized into reviewable PR-sized milestones aligned
to Wave 0 / Wave 1 / Wave 2 structure).
