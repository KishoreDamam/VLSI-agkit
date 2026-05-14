# Voltage Scaling, Dual-Edge Triggering, Terminations, and Decoupling

> Beyond clock control: four physical-level power techniques that show up
> in FPGA design. Each has a sharp trade-off — none is "free" power.

## Voltage scaling

Dynamic power scales as `V²·f`. Drop Vdd by 10 % → power drops by 19 %.
Drop by 20 % → 36 %. The quadratic makes voltage the strongest knob.

But: cell delay scales roughly as `Vdd / (Vdd − Vth)²` — drops *more
than* linearly when you reduce voltage. Max operating frequency falls
faster than power does.

| Vdd | Relative power | Relative Fmax |
|---|---|---|
| 1.0 (nominal) | 1.00 | 1.00 |
| 0.95 | 0.90 | 0.93 |
| 0.90 | 0.81 | 0.85 |
| 0.85 | 0.72 | 0.75 |
| 0.80 | 0.64 | 0.64 |

The crossover where you save 1 % power per 1 % frequency loss is
typically 5–10 % below nominal. Beyond that you're spending more Fmax
than you save power.

### Dynamic voltage / frequency scaling (DVFS)

When the workload is light, drop Vdd and clock frequency together. When
heavy, raise both. Saves power on average without the worst-case
penalty.

FPGAs supporting DVFS (Xilinx Versal, Intel Stratix 10) provide
voltage-controlled rails and frequency-controlled PLLs. Typical
software-mode policy:

```
if (utilization > 80%)      → 1.0 V, 500 MHz   (high-perf mode)
else if (util > 30%)        → 0.9 V, 400 MHz   (medium)
else                        → 0.8 V, 250 MHz   (low / idle)
```

### Caveats

- **STA must run at the lowest Vdd corner.** The slow-slow signoff
  view's voltage must include the lowest expected operating Vdd.
- **Process corners interact with voltage.** Slow-process + low-voltage
  is the worst-case setup; fast-process + high-voltage is the worst-case
  hold. See `sta/references/mmmc-corners.md`.
- **Vdd droop matters.** Voltage scaling reduces nominal Vdd; transient
  droop (caused by switching activity) can drop the supply below the
  STA corner. Decoupling (see below) becomes more critical.

## Dual-edge triggered flip-flops (DDR registers)

A flop that samples on *both* rising and falling clock edges captures
two data items per clock period. Same throughput at half the clock
frequency → half the clock-tree power.

```systemverilog
// Single-edge: must run at 500 MHz to throughput 500 Msps
always_ff @(posedge clk)
    out_se <= data_in;

// Dual-edge: 250 MHz clock, same 500 Msps throughput
// Only works if the FPGA has DDR primitives
ODDR2 u_oddr (
    .Q   (out_dr),
    .C0  (clk_250),
    .C1  (~clk_250),
    .D0  (data_in_first_half),
    .D1  (data_in_second_half),
    .CE  (1'b1)
);
```

### When DDR registers exist

- **Xilinx**: `IDDR`/`ODDR` (Spartan-3 onwards), `IDDRE1`/`ODDRE1`
  (UltraScale+).
- **Intel/Altera**: `altddio_in`/`altddio_out` (Stratix III onwards).
- **Coolrunner-II** *CoolClock* feature: divides incoming clock by 2 and
  converts flops automatically. Same external behaviour, half the
  internal clock-tree power.

### When DDR registers don't exist

If the technology has no DDR primitive, the synthesizer emulates with
two flops + a 2:1 mux + a phase-shifted clock generator. This *adds*
power instead of saving it — area, an extra clock, and a mux per
register. Synthesis tools should warn; verify by reading the synthesis
log before relying on DDR-style coding.

**Rule:** only code dual-edge triggers if the target FPGA has primitive
support and the synthesis tool maps to it.

### Where DDR registers actually pay off

- High-speed I/O (DDR3/DDR4 PHY) — natively double-data-rate, so DDR
  registers are mandatory regardless of power.
- High-throughput on-chip datapaths where the half-frequency clock
  reduces clock-tree power significantly.
- Not useful for most internal logic — only sensible at I/O or in
  dedicated DSP pipelines.

## Terminations

Resistive output terminations create steady-state power dissipation.
Three patterns:

### Pull-up / pull-down termination

A resistor between an output and Vdd (or GND). Current flows whenever
the output drives the opposite rail.

```
Vdd ─── Rpull ─── pin
                    └── FPGA output
```

Current = Vdd / Rpull when output drives low. For a 3.3 V output with
1 kΩ pull-up: 3.3 mA continuous when driving low. Sum across all such
outputs → significant.

**Mitigation:** size pull-up as large as possible while still meeting
rise-time requirement. Calculate: target rise time `t_r = 0.69 · R · C`
where C is the line capacitance. Solve for max R.

### Parallel (shunt) termination at receiver

Matches transmission line impedance for high-speed signals. Permanent
DC current when the output holds a value.

```
TX ──── line (Z₀=50 Ω) ──── RX
                            │
                            R_term (50 Ω)
                            │
                            GND  (or Vtt)
```

Continuous power = V² / R during DC state. For 1.5 V LVCMOS into 50 Ω:
45 mW per pin per active drive.

### Series termination at source (better for power)

Resistor in series at the driver; no DC current path.

```
TX ── R_s ─── line ─── RX (high-Z input)
```

Zero steady-state power. Trade-off:

- Initial reflection from receiver back to source.
- Attenuation through R_s during the transition.

For point-to-point signals where the receiver is the only sink, series
termination is the power-optimal choice. For bussed signals (multiple
receivers), parallel termination is required for signal integrity —
accept the power cost.

### Calibrated termination (DCI / OCT)

FPGAs offer on-die calibrated termination (Xilinx DCI, Intel OCT).
Termination is digitally calibrated to silicon process. Saves the
external resistor but doesn't change the power equation — DCI
parallel-termination still draws DC current.

**Power-optimal pattern**: source-series for unidirectional
point-to-point; parallel-DCI for high-speed bidirectional buses only;
no termination at all for low-speed signals.

## Decoupling capacitors (PCB level)

Switching activity in the FPGA draws current pulses from Vdd. Without
decoupling, Vdd droops on every pulse — droop amplitude depends on
inductance of the supply path.

```
   Vdd plane → L (via, trace) → FPGA Vdd pin
```

Droop = L · di/dt. For a Virtex-7 drawing 5 A peak with 1 nH path
inductance and 100 ns rise time: droop = 1 nH × (5/100ns) = 50 mV.
That's 5 % of a 1 V rail — STA corner crossed.

### Decoupling cap rule of thumb

Place capacitors of different values close to each FPGA Vdd pin:

| Capacitor | Range | Effective frequency |
|---|---|---|
| Bulk (electrolytic / tantalum) | 10–100 µF | DC – 100 kHz |
| Mid-frequency (ceramic) | 0.1–1 µF | 100 kHz – 10 MHz |
| High-frequency (ceramic) | 1–10 nF | 10 MHz – 100 MHz |
| Very high frequency | 10–100 pF | > 100 MHz |

Place high-frequency caps physically closest to the FPGA pin. Vias add
inductance that defeats the decoupling at high frequencies.

### Why this is a power topic

Inadequate decoupling means:

- Vdd droops on switching events → flops slower → STA fails or silicon
  hold-races.
- Compensating in design means lower Vdd target → wider margin → more
  static power.
- Switching noise propagates to clock PLL → jitter → uncertainty budget
  grows → wasted timing margin.

Good decoupling lets you run at the nominal voltage without margin →
your voltage-scaling savings actually realize on silicon.

## Combining techniques — a stack

A typical low-power FPGA design uses several techniques together:

1. **Clock gating** at the BUFGCE level for entire idle blocks.
2. **Clock enable** at the flop level for fine-grained gating.
3. **DDR registers** at I/O for half-frequency clock-tree.
4. **DVFS** at the SoC level for idle-mode voltage drop.
5. **Series termination** on point-to-point I/O for zero static drive
   power.
6. **Adequate decoupling** to make all of the above realize without
   margin.

No single technique buys more than 30–40 %; the stack of all five can
reach 60–70 % off the brute-force baseline.

## Common pitfalls

- **DDR registers coded but no DDR primitive available.** Synthesis
  emulates → more power, not less. Always check the synth report.
- **Voltage scaled but STA only at typical corner.** Silicon
  setup-fails at the new Vmin. Run MMMC at every operating point.
- **Pull-ups everywhere "for safety".** Each one is a DC current path.
  Use the smallest necessary value, and only on inputs that can float.
- **Series termination with multiple receivers.** Reflections corrupt
  data — series only works for one receiver.
- **Decoupling caps only in one value.** A single 0.1 µF doesn't decouple
  the high-frequency region; switching noise survives.
- **Decoupling caps far from the pin.** Trace inductance overwhelms the
  capacitor's impedance. Always place close to the via, vias close to
  the pin.

## Citations

- **Kilts**, *Advanced FPGA Design*, Wiley 2007, Chapters 3 and 19 —
  voltage scaling, dual-edge FFs, terminations, decoupling.
- **Xilinx UG471** — SelectIO Resources (Pull-up/pull-down, DCI).
- **Intel AN-583** — Designing Power-Supply Networks for High-Speed
  FPGAs.

## See also

- `clock-and-input-control.md` — the higher-leverage half of the
  low-power toolkit.
- `sta/references/mmmc-corners.md` — voltage corners for sign-off.
- `sta/references/clock-uncertainty.md` — jitter component of
  uncertainty budget benefits from clean Vdd.
