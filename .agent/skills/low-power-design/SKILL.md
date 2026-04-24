---
name: low-power-design
description: Low-power techniques including UPF, clock gating, and power optimization.
---

# Low-Power Design

> Techniques for reducing power consumption.

---

## Power Components

```
Total Power = Dynamic + Static

Dynamic = α × C × V² × f
- α: Activity factor
- C: Capacitance
- V: Voltage
- f: Frequency

Static = Leakage (process dependent)
```

---

## Clock Gating

### RTL Clock Gating

```systemverilog
// Tool-synthesized clock gate
always_ff @(posedge clk) begin
    if (enable)
        data <= new_data;
end

// Explicit ICG cell
logic gated_clk;
CLKGATE u_cg (.CK(clk), .E(enable), .ECK(gated_clk));

always_ff @(posedge gated_clk) begin
    data <= new_data;
end
```

### Synthesis Directive

```tcl
# Enable automatic clock gating
set_clock_gating_style -sequential_cell latch \
    -positive_edge_logic integrated \
    -control_point before

insert_clock_gating
```

---

## Operand Isolation

```systemverilog
// ❌ Multiplier always switching
assign product = a * b;

// ✅ Isolated when not needed
assign isolated_a = mult_en ? a : '0;
assign isolated_b = mult_en ? b : '0;
assign product = isolated_a * isolated_b;
```

---

## Power Domains (UPF)

### Basic UPF

```tcl
# Create power domains
create_power_domain PD_TOP -include_scope
create_power_domain PD_CORE \
    -elements {u_core} \
    -supply {primary}

# Supply nets
create_supply_net VDD
create_supply_net VDDL  # Low voltage
create_supply_net VSS

# Power switch
create_power_switch ps_core \
    -domain PD_CORE \
    -input_supply_port {in VDD} \
    -output_supply_port {out VDD_CORE} \
    -control_port {ctrl power_en} \
    -on_state {on_s in {ctrl}}
```

### Isolation

```tcl
set_isolation iso_core \
    -domain PD_CORE \
    -isolation_power_net VDD \
    -applies_to outputs \
    -clamp_value 0

set_isolation_control iso_core \
    -domain PD_CORE \
    -isolation_signal iso_en \
    -isolation_sense high
```

### Retention

```tcl
set_retention ret_core \
    -domain PD_CORE \
    -retention_power_net VDD

set_retention_control ret_core \
    -domain PD_CORE \
    -save_signal {save posedge} \
    -restore_signal {restore posedge}
```

---

## Voltage Scaling

### Multi-Vt

```
HVT: High Vt - Low leakage, slow
SVT: Standard Vt - Balanced
LVT: Low Vt - Fast, high leakage
```

### DVFS

```tcl
# Define voltage states
create_pst_file low_power.pst

# PST entry
add_pst_state "high_perf" -domain PD_CORE \
    -supply {VDD 1.0} -frequency 500MHz

add_pst_state "low_power" -domain PD_CORE \
    -supply {VDD 0.8} -frequency 200MHz
```

---

## Activity Reduction

| Technique | Method |
|-----------|--------|
| Data gating | Gate data when unused |
| Memory banking | Only access needed banks |
| Bus encoding | Gray, bus invert |
| Clock gating | Gate idle modules |

---

## Power Analysis

```tcl
# PrimeTime PX
read_saif activity.saif
update_power
report_power -hierarchy > power.rpt
```

---

## Best Practices

| Practice | Benefit |
|----------|---------|
| Clock gate idle logic | Reduce dynamic |
| Use multi-Vt | Balance speed/leakage |
| Minimize activity | Less switching |
| Power gate idle blocks | Zero leakage |
| Use low-voltage domains | V² reduction |
