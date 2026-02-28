# /brainstorm - VLSI Architecture Exploration

$ARGUMENTS

---

## Purpose

Explore requirements and architecture before implementation.

## Setup

Read the following files for context:
- `.agent/agents/orchestrator.md` for coordination patterns
- `.agent/skills/brainstorming/SKILL.md` for Socratic questioning techniques

## Behavior

1. **Ask clarifying questions**
   - What functionality?
   - FPGA or ASIC?
   - Interface requirements?
   - Performance goals?
   - Constraints?

2. **Explore options**
   - Architecture alternatives
   - Trade-offs (area vs speed vs power)
   - Risk areas

3. **Document decisions**
   - Summary of requirements
   - Chosen approach
   - Rationale

## Output Format

```markdown
## Brainstorm: [Topic]

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
