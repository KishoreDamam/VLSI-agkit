---
name: brainstorming
description: Use when starting a VLSI project before any RTL is written, or when requirements feel vague — clarifying architecture, interface, timing, and verification expectations through Socratic questioning.
---

# Brainstorming

> Ask the right questions before writing RTL.

---

## When to use

- Spec is a paragraph of prose, not a numbered list of requirements.
- "Just build me a FIFO" — but FIFO depth, clock domains, and overflow behavior are unspecified.
- Multiple interpretations of the spec are possible and the wrong one would be expensive to undo.
- Stakeholders disagree about scope and you need to surface the disagreement.

**Not for:** projects with a complete, signed-off MRD/spec (skip to `plan-writing` and `design`); minor RTL edits inside a known module.

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

---

## Anti-patterns (do NOT do this)

1. **Skipping straight to RTL.** "I'll figure it out as I code" turns into a rewrite when stakeholders disagree downstream.
2. **Asking only the design questions.** Verification, integration, and tape-out constraints reshape the architecture — surface them now.
3. **Yes/no questions when open-ended ones would expose more.** "Is throughput important?" → "What throughput in beats/sec at what clock?".
4. **Letting one stakeholder answer for the whole team.** Verification, FPGA, ASIC, and SW each have hard constraints; ask each.
5. **No artifact.** A brainstorm with no written output is a brainstorm you'll repeat in two weeks.

---

## Validation checklist (brainstorm "done" gate)

- [ ] Every category in the Socratic Gate has at least one concrete answer (not "TBD").
- [ ] Target (FPGA family / ASIC node) is named.
- [ ] Clock domains and reset strategy are decided.
- [ ] Verification approach (sim / formal / silicon) is named.
- [ ] At least one open question is logged with an owner and a deadline.
- [ ] The output is committed to the repo (markdown), not left in chat history.
