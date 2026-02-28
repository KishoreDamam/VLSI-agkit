# /integrate - IP Integration Workflow

$ARGUMENTS

---

## Purpose

Integrate IP cores and connect bus interfaces.

## Setup

Read the following files for integration guidance:
- `.agent/agents/ip-integrator.md` for integration methodology
- `.agent/skills/axi-protocols/SKILL.md` for AXI bus protocols
- `.agent/skills/ip-reuse/SKILL.md` for IP packaging standards
- `.agent/skills/clock-domain-crossing/SKILL.md` if crossing clock domains

## Behavior

1. **Analyze IP**
   - Read documentation / datasheet
   - Understand all interfaces (ports, protocols, clocking)

2. **Create wrappers**
   - Adapt interface mismatches
   - Handle CDC if needed
   - Add protocol bridges

3. **Connect**
   - Wire all signals in top-level
   - Verify connectivity
   - Add integration constraints

## Integration Steps

```
1. Study IP datasheet / interface spec
2. Map interfaces to system bus
3. Create wrapper if protocol/width mismatch
4. Instantiate and connect in top level
5. Add timing constraints for new paths
6. Verify integration with simulation
```

## Common Integration Tasks

| Task | Approach |
|---|---|
| Protocol mismatch | Add bridge (e.g., AXI-to-APB) |
| Width mismatch | Wrapper with width conversion |
| Clock domain crossing | Async FIFO or synchronizer |
| Reset polarity mismatch | Inverter in wrapper |
| Missing handshake | Add ready/valid adapter |

## Checklist

- [ ] All IPs instantiated correctly
- [ ] All interfaces connected (no floating ports)
- [ ] Clocks assigned to correct domains
- [ ] Resets connected with correct polarity
- [ ] Timing constraints updated for new paths
- [ ] Integration simulation passes
