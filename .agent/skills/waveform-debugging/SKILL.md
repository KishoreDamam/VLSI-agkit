---
name: waveform-debugging
description: Use when debugging from waveforms — VCD/FSDB dumping, selective dumping, signal tracing with `$display` or file logging, recognizing common bug patterns (X-propagation, off-by-one, glitches), or applying binary-search/reverse-trace debug strategies.
---

# Waveform Debugging

> Techniques for analyzing simulation waveforms.

---

## When to use

- A test fails and you have a VCD/FSDB but don't know which signal to look at first.
- Bug reproduces only at a specific time/cycle and you need to narrow down the cause.
- An `X` or `Z` propagates through the design and you need to trace its origin.
- Comparing a known-good run vs. a failing run to find the divergence point.
- Sim runtimes are dominated by waveform dumping; need to scope it down.

**Not for:** post-silicon debug (use ILA/logic analyzer); coverage-hole analysis (use the coverage report, not the waveform).

---

## Waveform Dumping

### VCD Format

```systemverilog
initial begin
    $dumpfile("waves.vcd");
    $dumpvars(0, tb_top);
end
```

### FSDB Format (Verdi)

```systemverilog
initial begin
    $fsdbDumpfile("waves.fsdb");
    $fsdbDumpvars(0, tb_top);
    $fsdbDumpSVA;  // Include assertions
end
```

### Selective Dumping

```systemverilog
// Dump only specific modules
$dumpvars(1, tb.dut.core);
$dumpvars(0, tb.dut.memory);

// Start/stop dumping
$dumpoff;  // Pause
$dumpon;   // Resume
```

---

## Signal Tracing

### Print Statements

```systemverilog
always @(posedge clk) begin
    if (error)
        $display("[%0t] ERROR: addr=%h data=%h",
                 $time, addr, data);
end

// Conditional trace
`ifdef DEBUG
    $display(...);
`endif
```

### File Logging

```systemverilog
integer log_file;
initial begin
    log_file = $fopen("debug.log", "w");
end

always @(posedge clk) begin
    $fwrite(log_file, "%0t: data=%h\n", $time, data);
end

final begin
    $fclose(log_file);
end
```

---

## Common Bug Patterns

| Pattern | What to Look For |
|---------|------------------|
| X values | Uninitialized or multi-driven |
| Glitches | Combinational hazards |
| Missing transactions | Check enables, handshakes |
| Wrong data | Trace data path |
| Timing issues | Check clock edges, setup/hold |

---

## Debug Strategies

### 1. Binary Search

```
Known good → Known bad
      ↓
   Check middle
      ↓
   Narrow down
      ↓
   Find exact cycle
```

### 2. Reverse Trace

```
Start at error
      ↓
Trace signal back
      ↓
Find source
      ↓
Identify cause
```

### 3. Compare Good vs Bad

```
Run passing test → Capture waveform
Run failing test → Capture waveform
Compare signals at divergence point
```

---

## Waveform Analysis Tips

| Look For | Indicates |
|----------|-----------|
| `X` | Uninitialized, multi-driven |
| Wrong timing | Clock/enable issues |
| No transitions | Stuck signal |
| Unexpected values | Logic bug |
| Metastability | CDC issue |

---

## Tools

| Tool | Usage |
|------|-------|
| GTKWave | View VCD |
| Verdi | View FSDB |
| nWave | Cadence waveform |
| Vivado Simulator | Xilinx |

---

## Anti-patterns (do NOT do this)

1. **Dumping the entire DUT for a long simulation.** VCDs become multi-GB; load times kill iteration speed. Scope dumps to the failing block.
2. **Staring at waveforms without a hypothesis.** Form a hypothesis first ("output should be 1 at cycle N"), then go to that signal at that time.
3. **Trusting the displayed value of an `X` source.** A red `X` hides whatever value drove it; trace upstream until you find the signal that's *not* `X`.
4. **Comparing waveforms by eye across long runs.** Use logfile diffs or compare-traces tools; eyeballs miss single-cycle drift.
5. **Adding `$display` permanently to RTL for debug.** Use a separate debug module or `ifdef DEBUG` — leftover `$display`s leak into release simulations and slow them down.

---

## Validation checklist

- [ ] Failing simulation produces a waveform reproducible from a known seed.
- [ ] Dump scope limited to the suspect hierarchy (not the whole DUT).
- [ ] Hypothesis written down before opening the waveform viewer.
- [ ] Origin of any `X`/`Z` traced to a specific RTL line, not just observed.
- [ ] If comparing good-vs-bad runs, divergence cycle identified before deeper analysis.
- [ ] Bug fix re-runs cleanly with the same testbench seed.
