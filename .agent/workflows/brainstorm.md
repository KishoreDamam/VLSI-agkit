---
description: Architecture exploration and requirements gathering for VLSI projects.
---

# /brainstorm - VLSI Architecture Exploration

$ARGUMENTS

---

## Purpose

Explore requirements and architecture before implementation.

## Resources

- **Lead agent:** `orchestrator` (routes to specialists for trade-off questions), `project-planner` (when output feeds a plan)
- **Supporting agents:** any specialist relevant to the domain (`rtl-designer`, `verification-engineer`, `timing-analyst`, `fpga-specialist`, `asic-specialist`, etc.)
- **Required skills:** `brainstorming` (Socratic question banks for VLSI: scope, interface, target, performance, constraints, reuse, verification)
- **Conditional skills:** `axi-protocols` / `clock-domain-crossing` / `low-power-design` etc. when domain-specific deep dives surface during exploration

---

## Behavior

1. **Ask clarifying questions**
   - What functionality?
   - FPGA or ASIC?
   - Interface requirements?
   - Performance goals?
   - Constraints?

2. **Explore options**
   - Architecture alternatives
   - Trade-offs
   - Risk areas

3. **Document decisions**
   - Summary of requirements
   - Chosen approach
   - Rationale

---

## Output Format

```markdown
## 🧠 Brainstorm: [Topic]

### Requirements
- [Requirement 1]
- [Requirement 2]

### Options Considered
1. **Option A**: [Description]
   - Pro: ...
   - Con: ...

2. **Option B**: [Description]
   - Pro: ...
   - Con: ...

### Recommendation
[Chosen approach and why]

### Open Questions
- [Question 1]
- [Question 2]
```

---

## Examples

```
/brainstorm DDR4 controller
/brainstorm FIFO architecture for CDC
/brainstorm AXI interconnect topology
```
