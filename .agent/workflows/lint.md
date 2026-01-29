---
description: Linting workflow for RTL code quality.
---

# /lint - RTL Linting Workflow

$ARGUMENTS

---

## Purpose

Check RTL code quality and catch common issues.

---

## Behavior

1. **Run lint tool**
   - Check for errors
   - Check for warnings

2. **Review results**
   - Critical issues
   - Best practice violations

3. **Fix issues**
   - Address errors first
   - Then warnings

---

## Common Lint Rules

| Rule | Issue |
|------|-------|
| LATCH | Latch inferred |
| MULTI_DRIVEN | Multiple drivers |
| WIDTH_MISMATCH | Bit width issue |
| UNUSED | Unused signal |
| CASE_INCOMPLETE | Missing case items |

---

## Tools

```bash
# Verilator
verilator --lint-only -Wall file.sv

# SpyGlass
spyglass -goal lint/lint_rtl

# Vivado
synth_design -rtl
```

---

## Checklist

- [ ] No errors
- [ ] Warnings reviewed
- [ ] Waivers documented

---

## Examples

```
/lint check for latches
/lint run full lint on module
/lint fix width mismatches
```
