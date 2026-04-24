---
description: Create project plan for VLSI tasks. No code - only plan file generation.
---

# /plan - VLSI Project Planning

$ARGUMENTS

---

## Purpose

Create a detailed task breakdown before implementation.

---

## Behavior

1. **Analyze request**
   - Scope
   - Complexity
   - Dependencies

2. **Create plan file**
   - Task breakdown
   - Phase structure
   - Deliverables

3. **Output location**
   - `docs/PLAN-{task-slug}.md`

---

## Plan Structure

```markdown
# [Project Name]

## Overview
[Brief description]

## Tasks

### Phase 1: Specification
- [ ] Define interfaces
- [ ] Architecture document

### Phase 2: RTL Design
- [ ] Module A
- [ ] Module B
- [ ] Integration

### Phase 3: Verification
- [ ] Testbench
- [ ] Test cases
- [ ] Coverage

### Phase 4: Implementation
- [ ] Synthesis
- [ ] Timing closure

## Deliverables
- [ ] RTL
- [ ] Testbench
- [ ] Documentation
```

---

## Examples

```
/plan DMA controller
/plan AXI-to-APB bridge
/plan packet processor
```
