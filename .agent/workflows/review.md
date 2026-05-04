---
description: Code review workflow with VLSI checklist.
---

# /review - RTL Code Review

$ARGUMENTS

---

## Purpose

Review RTL code for quality and correctness.

## Resources

- **Lead agent:** `lint-reviewer`
- **Supporting agents:** `rtl-designer` (architectural feedback), `verification-engineer` (testability and coverage gaps), `timing-analyst` (CDC and timing-flavored review)
- **Required skills:** `clean-rtl` (hygiene checklist), `systemverilog-coding` (language-level review)
- **Conditional skills:** `fsm-design` (state machines under review), `clock-domain-crossing` (multi-clock RTL), `axi-protocols` (bus-facing modules), `synthesis-guidelines` (synth-readiness)

---

## Behavior

1. **Check structure**
   - Module organization
   - Naming conventions
   - Comments

2. **Check logic**
   - Synthesizability
   - Reset
   - FSMs

3. **Check timing**
   - CDC handling
   - Pipelining

---

## Checklist

### Structure
- [ ] Standard naming
- [ ] Proper headers
- [ ] Clean organization

### Logic
- [ ] No latches
- [ ] Correct reset
- [ ] FSM with default

### Timing
- [ ] CDC synchronizers
- [ ] Registered outputs
- [ ] No combinational loops

---

## Output Format

```markdown
## Review: [Module]

### Summary
✅ Passed: X items
⚠️ Warnings: X items
❌ Issues: X items

### Issues
1. [File:Line] - [Issue]

### Recommendations
1. [Suggestion]
```

---

## Examples

```
/review dma_controller.sv
/review for CDC issues
/review check naming conventions
```
