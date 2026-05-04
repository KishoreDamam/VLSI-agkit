---
name: plan-writing
description: Use when breaking a VLSI project into a written plan — phase decomposition (spec, RTL, verification, implementation), deliverables, dependencies, and effort estimation.
---

# Plan Writing

> Break down VLSI tasks into manageable steps.

---

## When to use

- After `brainstorming` produced agreed requirements but before any RTL is written.
- A multi-week effort needs a written plan checked into the repo for review.
- You need to estimate effort for staffing or schedule alignment.
- Cross-team dependencies (verification, FPGA bring-up, software) must be made explicit.

**Not for:** single-PR changes (overhead exceeds value); ongoing maintenance work; tasks where the plan would be longer than the implementation.

---

## Plan Structure

```markdown
# [Task Name]

## Overview
[Brief description]

## Requirements
- [Requirement 1]
- [Requirement 2]

## Tasks

### Phase 1: Specification
- [ ] Define interfaces
- [ ] Document architecture
- [ ] Review with team

### Phase 2: RTL Design
- [ ] Implement module A
- [ ] Implement module B
- [ ] Integration

### Phase 3: Verification
- [ ] Create testbench
- [ ] Write tests
- [ ] Run regression

### Phase 4: Implementation
- [ ] Synthesis
- [ ] Timing closure

## Deliverables
- [ ] RTL code
- [ ] Testbench
- [ ] Documentation

## Dependencies
- [Dependency 1]
- [Dependency 2]
```

---

## Estimation Guide

| Task | Effort |
|------|--------|
| Simple module | 1-2 days |
| Complex module | 3-5 days |
| FSM | 1-2 days |
| Testbench | 2-4 days |
| Integration | 1-2 days |

---

## Best Practices

- Break into small, testable units
- Include verification in plan
- Add buffer for issues
- Define clear milestones

---

## Anti-patterns (do NOT do this)

1. **Phase 4: "Tape-out" with no detail.** Implementation/timing/DFT each have their own gates; flatten them out.
2. **No verification phase, or "verify" as a single line item.** Coverage, regression, formal, GLS — name each.
3. **Tasks without owners.** "Implement module A" is not actionable until a name is attached.
4. **Estimates without buffer for first-bug closure.** First silicon bring-up always finds something; budget for it.
5. **Plan committed to a wiki / shared drive instead of the repo.** It drifts; keep the plan next to the RTL.
6. **No exit criterion per phase.** "Done" must be objective (lint clean, regression PASS, WNS ≥ 0), not "looks good".

---

## Validation checklist (plan "done" gate)

- [ ] Every phase has objective entry and exit criteria.
- [ ] Verification phase names sim, formal (if any), regression scope, and coverage target.
- [ ] Implementation phase covers synth, timing, lint/CDC, and (for ASIC) DFT.
- [ ] Every task has an owner and a rough estimate (days/weeks).
- [ ] External dependencies (IP delivery, board availability, tool licenses) are listed.
- [ ] Plan is committed to the repo (`docs/plans/<name>.md` or equivalent) and linked from a top-level README or tracker.
- [ ] Risks logged with mitigation owners.
