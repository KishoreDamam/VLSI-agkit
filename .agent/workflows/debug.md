---
description: Debug workflow with waveform analysis and root cause investigation.
---

# /debug - VLSI Debug Workflow

$ARGUMENTS

---

## Purpose

Systematic investigation of VLSI bugs.

## Resources

- **Lead agent:** `debugger`
- **Supporting agents:** `verification-engineer` (testbench fixes), `rtl-designer` (RTL fixes), `timing-analyst` (when failure has timing flavor), `ip-integrator` (IP-boundary issues)
- **Required skills:** `waveform-debugging` (VCD/FSDB navigation, X-tracing, binary search)
- **Conditional skills:** `clock-domain-crossing` (CDC-related corruption), `formal-verification` (assertion coverage gaps), `axi-protocols` (handshake hangs), `fsm-design` (illegal state debug), `tcl-scripting` (Tcl-driven debug automation)

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
