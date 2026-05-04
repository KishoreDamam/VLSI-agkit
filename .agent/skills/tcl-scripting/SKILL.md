---
name: tcl-scripting
description: Use when writing Tcl for EDA tools (Vivado, Design Compiler, Quartus) — variables, lists, file I/O, control flow, procedures, or tool-specific command idioms.
---

# Tcl Scripting

> Tcl patterns for EDA tool automation.

---

## When to use

- Automating a Vivado/Quartus/DC/Genus build, run, or report step.
- Looking up Tcl syntax that's specifically used inside EDA-tool consoles.
- Writing reusable `procs` for project setup, regression launching, or report parsing.
- Debugging Tcl errors from synth/sim scripts (variable scoping, list vs string, `expr` precision).

**Not for:** general Tcl programming (use the official Tcl docs); long pipelines that fight Tcl's data model (write the orchestration layer in Python and call Tcl only at the tool boundary).

---

## Basics

```tcl
# Variables
set my_var "value"
set width 32

# String interpolation
set msg "Width is $width"

# No interpolation
set pattern {[0-9]+}

# Math
set result [expr {$a + $b}]

# Lists
set files {file1.sv file2.sv file3.sv}
lappend files file4.sv
foreach f $files { puts $f }
```

---

## File Operations

```tcl
# Glob files
set sources [glob ./rtl/*.sv]
set all_rtl [glob -nocomplain ./rtl/**/*.sv]

# Read file
set fp [open "config.txt" r]
set content [read $fp]
close $fp

# Write file
set fp [open "output.txt" w]
puts $fp "content"
close $fp
```

---

## Control Flow

```tcl
# If/else
if {$width == 32} {
    puts "32-bit"
} elseif {$width == 64} {
    puts "64-bit"  
} else {
    puts "Other"
}

# Loop
foreach item $list {
    puts $item
}

for {set i 0} {$i < 10} {incr i} {
    puts $i
}

while {$running} {
    # do work
}
```

---

## Procedures

```tcl
proc add_source {file} {
    global sources
    lappend sources $file
    puts "Added: $file"
}

proc compile_design {top {effort "high"}} {
    puts "Compiling $top with $effort effort"
    # ...
}

# Call
compile_design "my_top"
compile_design "my_top" "medium"
```

---

## EDA-tool Tcl idioms

These patterns recur across Vivado, DC, Genus, Quartus, and JasperGold. Tool-specific command sequences live in the per-tool flow skills (`vivado-flow`, `quartus-flow`, `synopsys-flow`, `cadence-flow`).

```tcl
# Iterate a Tcl collection (pins/cells/nets) — collections are NOT lists
foreach_in_collection cell [get_cells -hier *] {
    set name [get_property full_name $cell]
    # ...
}

# Filter by attribute
set ff_cells [filter_collection [get_cells -hier *] "is_sequential == true"]

# Walk a hierarchy
foreach inst [get_cells -hier -filter {ref_name =~ "*FIFO*"}] { ... }

# Read attributes safely
if {[llength [get_property -quiet name $obj]] == 0} { ... }

# Export reports with timestamps for traceability
set ts [clock format [clock seconds] -format "%Y%m%d_%H%M%S"]
report_timing > rpt/timing_${ts}.rpt
```

---

## Useful Commands

| Command | Purpose |
|---------|---------|
| `glob` | Find files |
| `file exists` | Check file |
| `file mkdir` | Create directory |
| `exec` | Run shell command |
| `catch` | Error handling |
| `puts` | Print output |
| `source` | Run Tcl file |

---

## Error Handling

```tcl
if {[catch {risky_command} err]} {
    puts "Error: $err"
    # Handle error
} else {
    puts "Success"
}
```

---

## Anti-patterns (do NOT do this)

1. **Double-quoting commands you mean to evaluate.** `puts "[get_cells *]"` works; `puts "{get_cells *}"` prints the literal. Curly braces suppress substitution.
2. **Using `==` for strings.** Tcl's `==` is numeric only; use `eq`/`ne` for strings.
3. **Forgetting that `expr` is the only way to do math.** `set x [expr {$a + $b}]` — and always brace the expression so Tcl doesn't double-substitute.
4. **Returning lists by `return $list` and reading them as strings.** Use `lindex` / `foreach`, not `string` ops.
5. **Hardcoding Vivado/DC paths in the script.** Take them from environment or a `config.tcl`.
6. **Silently swallowing tool errors.** Always check `catch` return code; let CI fail fast.
7. **Writing 200-line `proc`s.** Tcl debug is hard enough — keep procs short and pure.

---

## Validation checklist

- [ ] Every script runs from a fresh shell (no reliance on prior environment).
- [ ] All paths come from arguments or environment, not hardcoded site-specific strings.
- [ ] Error from a tool command (`synth_design`, `read_verilog`, etc.) terminates the script with a non-zero exit code.
- [ ] `expr` arguments are braced (`{...}`) to avoid double substitution.
- [ ] No use of `==`/`!=` on strings (use `eq`/`ne`).
- [ ] Reports written to a known output directory, with timestamps if reproducibility matters.
