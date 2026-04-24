# /debug - VLSI Debug Workflow

$ARGUMENTS

---

## Purpose

Systematic investigation of VLSI bugs with waveform analysis.

## Setup

Read the following files for debug techniques:
- `.agent/agents/debugger.md` for debug methodology
- `.agent/skills/waveform-debugging/SKILL.md` for waveform analysis patterns

## Behavior

1. **Reproduce**
   - Get exact failure scenario
   - Capture waveform (VCD/FSDB)

2. **Isolate**
   - Which module is failing?
   - Which signal diverges from expected?

3. **Trace**
   - Follow data flow backward from failure
   - Find the first point of divergence

4. **Fix**
   - Root cause fix (not a workaround)
   - Add assertion to prevent regression

## Debug Steps

```
1. Run simulation that reproduces the failure
2. Open waveform viewer (GTKWave, Verdi, Vivado)
3. Find the failing output signal
4. Trace backward to find source of bad data
5. Identify root cause
6. Apply fix and verify
7. Add assertion to catch future regressions
```

## Common Bug Patterns

| Pattern | Symptom | Check |
|---|---|---|
| Race condition | Intermittent failures | Clock edge alignment |
| Reset issue | Wrong initial values | Reset coverage |
| X-propagation | Unknown values | X-handling in sim |
| CDC violation | Data corruption across domains | Synchronizer presence |
| Off-by-one | Data shifted by 1 cycle | Pipeline stage count |

## Output Format

```markdown
## Debug: [Issue]

### Symptom
[What is happening]

### Investigation
- Traced signal X: [observed vs expected]
- Found issue at: [module:line]

### Root Cause
[Why this happened]

### Fix
[What was changed and why]

### Regression Prevention
[Assertion added]
```
