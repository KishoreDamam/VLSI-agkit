# /review - RTL Code Review

$ARGUMENTS

---

## Purpose

Review RTL code for quality, correctness, and best practices.

## Setup

Read the following files for review standards:
- `.agent/agents/lint-reviewer.md` for review methodology
- `.agent/skills/clean-rtl/SKILL.md` for coding standards

## Behavior

1. **Check structure**
   - Module organization (7-section template)
   - Naming conventions (i_/o_ ports, UPPER params, name_t types)
   - Header comments

2. **Check logic**
   - Synthesizability (no latches, no combinational loops)
   - Reset handling (all registers reset)
   - FSM completeness (default state, unreachable handling)

3. **Check timing**
   - CDC synchronizers present where needed
   - Registered outputs on module boundaries
   - No combinational loops

## Review Checklist

### Structure
- [ ] Standard naming conventions
- [ ] Proper module header
- [ ] Clean section organization
- [ ] Parameterized widths

### Logic
- [ ] No latches inferred
- [ ] Correct reset (sync/async as appropriate)
- [ ] FSMs have default state
- [ ] Complete case statements
- [ ] Width matching in assignments

### Timing
- [ ] CDC synchronizers present
- [ ] Registered module outputs
- [ ] No combinational feedback loops
- [ ] Clock gating done properly

## Output Format

```markdown
## Review: [Module Name]

### Summary
- Passed: X items
- Warnings: X items
- Issues: X items

### Issues Found
1. [file:line] - [Description of issue]

### Recommendations
1. [Suggestion for improvement]
```
