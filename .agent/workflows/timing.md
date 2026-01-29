---
description: Timing analysis workflow for timing closure.
---

# /timing - Timing Analysis Workflow

$ARGUMENTS

---

## Purpose

Analyze and close timing issues.

---

## Behavior

1. **Run STA**
   - Check setup/hold
   - Review reports

2. **Identify issues**
   - Critical paths
   - Violations

3. **Fix**
   - Pipeline
   - Constraint changes
   - RTL changes

---

## Key Metrics

| Metric | Goal |
|--------|------|
| WNS | > 0 |
| TNS | 0 |
| WHS | > 0 |
| THS | 0 |

---

## Fixing Violations

| Issue | Solution |
|-------|----------|
| Setup violation | Pipeline, optimize logic |
| Hold violation | Add delay |
| High fanout | Buffer, clone |
| Long path | Floorplan |

---

## Examples

```
/timing analyze critical paths
/timing fix setup violation on data bus
/timing add multicycle path for slow logic
```
