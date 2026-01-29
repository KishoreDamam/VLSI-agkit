---
description: IP integration workflow for connecting blocks and buses.
---

# /integrate - IP Integration Workflow

$ARGUMENTS

---

## Purpose

Integrate IP cores and connect bus interfaces.

---

## Behavior

1. **Analyze IP**
   - Read documentation
   - Understand interfaces

2. **Create wrappers**
   - Adapt interfaces
   - Handle CDC

3. **Connect**
   - Wire signals
   - Verify connectivity

---

## Integration Steps

```
1. Study IP datasheet
2. Map interfaces
3. Create wrapper if needed
4. Connect in top level
5. Add constraints
6. Verify integration
```

---

## Common Tasks

| Task | Approach |
|------|----------|
| Protocol mismatch | Add bridge |
| Width mismatch | Wrapper with conversion |
| Clock domain | Async FIFO or sync |
| Reset polarity | Inverter in wrapper |

---

## Checklist

- [ ] All IPs instantiated
- [ ] Interfaces connected
- [ ] Clocks assigned
- [ ] Resets connected
- [ ] Constraints updated

---

## Examples

```
/integrate DDR controller with AXI fabric
/integrate PCIe endpoint
/integrate clock wizard IP
```
