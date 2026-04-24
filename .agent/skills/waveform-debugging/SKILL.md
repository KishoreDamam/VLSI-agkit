---
name: waveform-debugging
description: Waveform analysis and debug techniques.
---

# Waveform Debugging

> Techniques for analyzing simulation waveforms.

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
