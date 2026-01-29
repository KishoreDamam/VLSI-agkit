---
description: Debug workflow with waveform analysis and root cause investigation.
---

# /debug - VLSI Debug Workflow

$ARGUMENTS

---

## Purpose

Systematic investigation of VLSI bugs.

---

## Behavior

1. **Reproduce**
   - Get exact failure
   - Capture waveform

2. **Isolate**
   - Which module?
   - Which signal?

3. **Trace**
   - Follow data flow
   - Find divergence

4. **Fix**
   - Root cause fix
   - Add assertion

---

## Debug Steps

```
1. Run simulation with failure
2. Open waveform viewer
3. Find failing signal
4. Trace back to source
5. Identify root cause
6. Fix and verify
```

---

## Output Format

```markdown
## 🔍 Debug: [Issue]

### Symptom
[What is happening]

### Investigation
- Traced signal X: [value]
- Found issue at: [location]

### Root Cause
[Why this happened]

### Fix
[What was changed]
```

---

## Examples

```
/debug FIFO underflow
/debug wrong data on output
/debug timing failure in CDC
```
