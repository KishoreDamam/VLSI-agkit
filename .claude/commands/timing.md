# /timing - Timing Analysis Workflow

$ARGUMENTS

---

## Purpose

Analyze and close timing issues in VLSI designs.

## Setup

Read the following files for timing guidance:
- `.agent/agents/timing-analyst.md` for timing analysis methodology
- `.agent/skills/timing-constraints/SKILL.md` for SDC/XDC constraints
- `.agent/skills/clock-domain-crossing/SKILL.md` if CDC issues are involved

## Behavior

1. **Run STA**
   - Check setup/hold violations
   - Review timing reports

2. **Identify issues**
   - Critical paths
   - Worst negative slack
   - CDC paths

3. **Fix violations**
   - Pipeline long paths
   - Adjust constraints
   - RTL changes if needed

## Key Metrics

| Metric | Description | Goal |
|---|---|---|
| WNS | Worst Negative Slack (setup) | > 0 |
| TNS | Total Negative Slack | = 0 |
| WHS | Worst Hold Slack | > 0 |
| THS | Total Hold Slack | = 0 |

## Fixing Violations

| Issue | Solution |
|---|---|
| Setup violation | Pipeline, optimize combinational logic, retiming |
| Hold violation | Add delay buffers |
| High fanout | Buffer insertion, register duplication |
| Long routing path | Floorplan constraints, placement guides |
| CDC violation | Add proper synchronizer, use async FIFO |

## Timing Fundamentals

```
Setup: T_clk > T_cq + T_comb + T_setup
Hold:  T_cq + T_comb > T_hold
```
