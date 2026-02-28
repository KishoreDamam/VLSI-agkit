# /lint - RTL Linting Workflow

$ARGUMENTS

---

## Purpose

Check RTL code quality and catch common issues before simulation.

## Setup

Read the following files for lint rules:
- `.agent/agents/lint-reviewer.md` for review methodology
- `.agent/skills/clean-rtl/SKILL.md` for coding standards

## Behavior

1. **Run lint check**
   - Analyze RTL for errors and warnings
   - Check against clean-rtl standards

2. **Review results**
   - Critical issues first
   - Best practice violations
   - Naming convention compliance

3. **Fix issues**
   - Address errors first
   - Then warnings
   - Document any waivers

## Common Lint Rules

| Rule | Issue | Severity |
|---|---|---|
| LATCH | Latch inferred from incomplete logic | Critical |
| MULTI_DRIVEN | Signal driven from multiple sources | Critical |
| WIDTH_MISMATCH | Bit width mismatch in assignment | Warning |
| UNUSED | Unused signal or port | Warning |
| CASE_INCOMPLETE | Missing case items or default | Warning |
| COMBO_LOOP | Combinational feedback loop | Critical |

## Tool Commands

```bash
# Verilator
verilator --lint-only -Wall file.sv

# SpyGlass
spyglass -goal lint/lint_rtl

# Vivado
synth_design -rtl
```

## Checklist

- [ ] No critical errors
- [ ] All warnings reviewed
- [ ] Naming conventions followed
- [ ] No latches inferred
- [ ] Waivers documented for accepted warnings
