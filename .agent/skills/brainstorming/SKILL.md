---
name: brainstorming
description: Socratic questioning for VLSI projects. Clarify requirements before design.
---

# Brainstorming

> Ask the right questions before writing RTL.

---

## Socratic Gate

Before starting any design, ask:

| Category | Questions |
|----------|-----------|
| **Scope** | What functionality? What's in/out of scope? |
| **Interface** | What bus protocol? Data widths? Handshaking? |
| **Target** | FPGA or ASIC? Which device/process? |
| **Performance** | Clock frequency? Latency? Throughput? |
| **Constraints** | Area limits? Power budget? |
| **Reuse** | Existing IPs to use? Future reuse needs? |

---

## Design Questions

### Architecture

- Block diagram?
- Data flow?
- Control flow?
- Clock domains?
- Reset strategy?

### Interface

- Protocol? (AXI, AHB, custom)
- Data width?
- Handshake? (valid/ready, req/ack)
- Backpressure handling?

### Timing

- Target frequency?
- Latency requirements?
- Pipeline depth?

---

## Verification Questions

- How to verify?
- Expected coverage?
- Existing testbenches?
- Reference model?

---

## Document Decisions

After brainstorming, document:

1. **Requirements** - What must it do
2. **Architecture** - How it does it
3. **Interfaces** - How it connects
4. **Constraints** - What limits apply
