---
name: formal-verification
description: Use when writing SystemVerilog Assertions (immediate or concurrent), property/sequence operators, assumption and cover setup for formal tools (JasperGold, VC Formal), or assertion patterns for handshakes, FIFOs, or AXI.
---

# Formal Verification

> Assertion-based verification and formal methods.

---

## When to use

- Proving control-path properties on FSMs, arbiters, FIFOs, and protocol interfaces.
- Writing SVA (immediate `assert`/concurrent `property`) inside RTL or as a bind module.
- Setting up assumptions/covers for formal tools (JasperGold, VC Formal, Symbiyosys).
- Closing coverage holes that simulation can't reach (deep state, rare interleavings).

**Not for:** datapath equivalence (use LEC); large arithmetic units (state explosion); replacing functional simulation entirely.

---

## Assertion Types

| Type | Syntax | Use |
|------|--------|-----|
| Immediate | `assert (expr)` | Procedural check |
| Concurrent | `assert property (p)` | Temporal check |
| Assume | `assume property (p)` | Constrain inputs |
| Cover | `cover property (p)` | Reachability |

---

## Immediate Assertions

```systemverilog
// Simple check
always_comb begin
    assert (count <= MAX_COUNT)
        else $error("Count overflow: %d", count);
end

// With action blocks
always @(posedge clk) begin
    assert (valid |-> !$isunknown(data))
        else begin
            $error("X on data when valid");
            $display("Time: %0t, data: %h", $time, data);
        end
end
```

---

## Concurrent Assertions

### Basic Properties

```systemverilog
// Implication: if A then B
property p_req_ack;
    @(posedge clk) disable iff (!rst_n)
    req |-> ##[1:5] ack;
endproperty
assert property (p_req_ack);

// Stable during transaction
property p_data_stable;
    @(posedge clk) disable iff (!rst_n)
    valid && !ready |=> $stable(data);
endproperty
assert property (p_data_stable);
```

### Sequence Operators

| Operator | Meaning |
|----------|---------|
| `##N` | N cycle delay |
| `##[M:N]` | M to N cycle delay |
| `[*N]` | N consecutive repetitions |
| `[*M:N]` | M to N repetitions |
| `\|->` | Overlapping implication |
| `\|=>` | Non-overlapping implication |

---

## Common Patterns

### Handshake

```systemverilog
// Valid must stay until ready
property p_valid_until_ready;
    @(posedge clk) disable iff (!rst_n)
    valid && !ready |=> valid;
endproperty

// Data stable while valid
property p_data_stable;
    @(posedge clk) disable iff (!rst_n)
    valid && !ready |=> $stable(data);
endproperty
```

### FIFO

```systemverilog
// Never write when full
property p_no_write_full;
    @(posedge clk) disable iff (!rst_n)
    full |-> !wr_en;
endproperty

// Never read when empty
property p_no_read_empty;
    @(posedge clk) disable iff (!rst_n)
    empty |-> !rd_en;
endproperty
```

### AXI

```systemverilog
// AWVALID stable until AWREADY
property p_axi_awvalid;
    @(posedge aclk) disable iff (!aresetn)
    awvalid && !awready |=> awvalid;
endproperty

// Write response after write
property p_axi_bresp;
    @(posedge aclk) disable iff (!aresetn)
    wvalid && wready && wlast |-> ##[1:$] bvalid;
endproperty
```

---

## Formal Tool Usage

### Assumptions

```systemverilog
// Constrain inputs for formal
assume property (@(posedge clk) disable iff (!rst_n)
    $onehot0(sel));

// Environment constraint
assume property (@(posedge clk)
    req |=> ##[0:3] ack);
```

### Cover Points

```systemverilog
// Verify reachability
cover property (@(posedge clk)
    (state == IDLE) ##[1:10] (state == DONE));

// Interesting scenario
cover property (@(posedge clk)
    full && wr_en |-> ##1 !full);
```

---

## SystemVerilog Assertion Library (SVA)

### Built-in Functions

| Function | Purpose |
|----------|---------|
| `$rose(sig)` | Rising edge |
| `$fell(sig)` | Falling edge |
| `$stable(sig)` | No change |
| `$changed(sig)` | Value changed |
| `$past(sig, N)` | Value N cycles ago |
| `$onehot(sig)` | Exactly one bit set |
| `$onehot0(sig)` | Zero or one bit |
| `$isunknown(sig)` | Contains X or Z |

---

## Best Practices

| Practice | Reason |
|----------|--------|
| Reset disable | Avoid false failures |
| Meaningful names | Documentation |
| Cover properties | Prove reachability |
| Avoid $past deeply | Tool performance |
| Group related assertions | Maintainability |

---

## Anti-patterns (do NOT do this)

1. **Asserting on data values you can't constrain.** A property `assert(out == expected)` with no model of `expected` will fire forever; instead assert *relationships* (handshake, ordering, exclusivity).
2. **Forgetting `disable iff (rst)`.** Reset windows trigger phantom failures that mask real bugs.
3. **Replacing assumptions with assertions on inputs.** Inputs need `assume`; only DUT outputs are `assert`. Confusing the two either over-constrains the proof or proves nothing.
4. **Deep `$past(sig, N)` chains.** Each step expands BMC state; rewrite as a small auxiliary register.
5. **Empty cover bin.** Properties that are vacuously true still pass — always pair `assert` with a `cover` that proves the antecedent is reachable.

---

## Validation checklist

- [ ] Every concurrent property has `disable iff (!rst_n)` (or equivalent).
- [ ] Inputs are constrained with `assume`; outputs proven with `assert`.
- [ ] Every `assert` has a paired `cover` showing the precondition fires.
- [ ] No properties depend on un-modeled external state (memory contents, etc.).
- [ ] Bound depth set explicitly; tool reports proven (not bounded-only) for safety properties where possible.
- [ ] Counter-examples reviewed — failure means a real bug or a missing assumption, not "tighten the assertion".
