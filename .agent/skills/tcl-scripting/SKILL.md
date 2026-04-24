---
name: tcl-scripting
description: Tcl scripting for EDA tools.
---

# Tcl Scripting

> Tcl patterns for EDA tool automation.

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

## EDA Tool Patterns

### Vivado

```tcl
# Create project
create_project proj ./proj -part xc7a100t

# Add files
add_files [glob ./rtl/*.sv]
set_property top top_module [current_fileset]

# Run flow
launch_runs synth_1
wait_on_run synth_1
launch_runs impl_1 -to_step write_bitstream
wait_on_run impl_1
```

### Design Compiler

```tcl
# Read design
analyze -format sverilog [glob rtl/*.sv]
elaborate top_module
link

# Compile
compile_ultra

# Report
report_timing > timing.rpt
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
