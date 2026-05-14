# Modal Constraints — `set_case_analysis` and Multi-Mode SDC

> A real chip has multiple usage modes: functional, scan-shift, BIST,
> sleep, debug. Each mode has different active clocks, different active
> paths, different timing requirements. SDC must reflect the mode being
> analyzed or you over-constrain / under-constrain silently.

## Why modes matter

Consider a chip with one CLK pin. In functional mode it runs at 1 GHz;
in scan-shift mode at 25 MHz. The path from `F1/Q` to `F2/SI` exists in
*scan* mode only; the path from `F1/Q` to `F3/D` exists in *functional*
mode only.

If you write one SDC that just declares both clocks on CLK:

```tcl
create_clock -name SysClk  -period 1.0  [get_ports CLK]
create_clock -name TestClk -period 40.0 [get_ports CLK]
```

…STA times the scan path against SysClk (1 ns — impossible to meet) and
the functional path against TestClk (over-relaxed — 40 ns is trivial).
Both wrong. You either need:

- **Single-mode SDC** — one SDC per mode, analyzed independently.
- **Merged SDC with case analysis** — one SDC, `set_case_analysis` pins
  the mode-select inputs so STA only analyzes the active mode.

## Single-mode vs merged-mode

| Approach | Pros | Cons |
|---|---|---|
| **Single-mode** (one SDC per mode) | Each SDC is simple; intent matches RTL designer's mental model | Multiple files to maintain; mode-coverage must be enforced by methodology |
| **Merged-mode** (one SDC, case analysis) | One source of truth; flow tool sees all modes at once | Harder to read; debugging requires understanding case-propagation |

Front-end designers prefer single-mode (closer to RTL). Back-end /
implementation prefers merged-mode (single tool invocation). Most teams
maintain single-mode SDCs and *generate* the merged SDC for sign-off.

## `set_case_analysis` — pinning a value

```tcl
set_case_analysis value port_pin_list
```

`value` is `0`, `1`, `rising`, or `falling`.

```tcl
# Pin scan-enable to 0 — selects functional mode
set_case_analysis 0 [get_ports scan_en]

# Pin a config register output to 1
set_case_analysis 1 [get_pins config_reg[3]/Q]

# 8-bit config register sets a specific mode
foreach {bit val} {0 0  1 1  2 1  3 0  4 1  5 0  6 1  7 0} {
    set_case_analysis $val [get_pins config_reg[$bit]/Q]
}
```

Three things happen when you set a pin to a constant:

1. **The pin emits no transitions.** Any timing arc starting at that
   pin is killed.
2. **The constant propagates through combinational logic.** A
   downstream pin whose value becomes fully determined also becomes
   constant.
3. **Logic gates with a controlling input fixed disable other arcs.**
   E.g., AND gate with one input = 0 → output forced to 0 → all paths
   through that AND are removed from timing.

```
   set_case_analysis 0 [get_ports A]
                              │
                              ▼
   A=0  ─┐
         AND ──── 0 ─── any logic downstream blocked
   B    ─┘
```

This propagation is what makes case analysis powerful. One
`set_case_analysis` on the mode-select pin can quiet thousands of
inactive paths — without listing them individually.

## Typical multi-mode SDC structure

### Functional mode

```tcl
# common.sdc — clocks always present
create_clock -name SysClk  -period 1.0  [get_ports CLK]
create_clock -name TestClk -period 40.0 [get_ports CLK]
set_clock_groups -physically_exclusive \
    -group [get_clocks SysClk] -group [get_clocks TestClk]

# I/O delays — common across modes (or split if mode-specific)
source io_delays.sdc

# Functional mode case
set_case_analysis 0 [get_ports scan_en]
set_case_analysis 0 [get_ports test_mode]
```

### Scan-shift mode

```tcl
# common.sdc — same as above
source common.sdc

# Scan mode case
set_case_analysis 1 [get_ports scan_en]
set_case_analysis 1 [get_ports test_mode]

# Scan-shift may need looser I/O timings
source io_delays_scan.sdc
```

### Merged mode (for tool invocation)

```tcl
# All clocks declared; no set_case_analysis here.
create_clock ...
create_generated_clock ...

# False paths cover what set_case_analysis would have killed
set_false_path -from [get_clocks SysClk]  -to [get_pins *_reg/SI]
set_false_path -from [get_clocks TestClk] -to [get_pins *_reg/D]
```

Merged-mode replaces `set_case_analysis` with `set_false_path` /
`set_clock_groups -physically_exclusive` — analyses both modes
simultaneously but loses the propagation magic. You must enumerate the
exception list manually.

## Where to apply `set_case_analysis`

- **Top-level ports** for global mode signals (`scan_en`, `test_mode`,
  `sleep`).
- **Register Q pins** for configuration registers that hold the mode
  setting after boot.

Avoid applying on:

- Internal combinational nodes — fragile to RTL changes that rename or
  optimize the net.
- Clock pins — that's not what case analysis is for; use
  `set_clock_groups` or `set_clock_sense -stop_propagation`.

## Mode-specific clocks (the CLK-pin example)

A single CLK port carrying different clocks in different modes:

```tcl
# Functional mode
create_clock -name SysClk -period 1.0 [get_ports CLK]
set_case_analysis 0 [get_ports scan_en]
```

```tcl
# Scan mode
create_clock -name TestClk -period 40.0 [get_ports CLK]
set_case_analysis 1 [get_ports scan_en]
```

In each single-mode SDC there is *one* `create_clock` on the CLK pin —
the right one for that mode. The case analysis pin's value selects
which paths are valid.

If you merge into one SDC with both `create_clock` declarations, STA
sees two clocks on the same port. Add the proper exclusivity:

```tcl
set_clock_groups -physically_exclusive \
    -group [get_clocks SysClk] -group [get_clocks TestClk]
```

…and the relevant scan-path exceptions
(`set_false_path -from SysClk -to *_reg/SI`).

## Sign-off matrix

A typical sign-off matrix multiplies modes × MMMC corners:

| Mode | PVT | RC | View name |
|---|---|---|---|
| Functional | SS (setup) | C_w-R_w | func_setup_ss_cw |
| Functional | FF (hold) | C_b-R_b | func_hold_ff_cb |
| Scan-shift | SS (setup) | C_w-R_w | scan_setup_ss_cw |
| Scan-shift | FF (hold) | C_b-R_b | scan_hold_ff_cb |
| BIST | TT | typical | bist_typ |

Each row is an MMMC view; the mode-specific SDC and corner-specific
library set drive the view. See `sta` skill
`references/mmmc-corners.md` for the corner-picking guide.

## Debugging case analysis

```tcl
report_case_analysis           ;# list all set_case_analysis in effect
report_case_analysis -status   ;# show propagated constants

# Check what got disabled
report_disable_timing
```

If a path you expected to be timed isn't showing up: trace its
endpoints; one of them likely has a constant propagated to its `D` pin
(or a controlling input of a gate in its cone is constant). The
propagation map from `report_case_analysis -status` will pinpoint the
source pin.

## Common pitfalls

- **One SDC for all modes.** Mode-select pins not pinned → STA times
  scan paths in functional mode and vice versa. Either case-analyze or
  false-path.
- **Forgetting `set_clock_groups -physically_exclusive` in merged SDC.**
  Two clocks on one port without exclusivity → STA times every pairing,
  triples runtime, false violations.
- **Case analysis on internal nets.** RTL rename or synthesis
  optimization → constraint silently dangling. Use top-level ports or
  register Q pins.
- **Conflicting case analyses across modes' SDCs.** If you split SDCs
  per mode but the build script accidentally sources both, you get
  contradictory pins. Audit `report_case_analysis`.
- **Case analysis vs `set_disable_timing`.** Both can disable paths,
  but they propagate differently. Case analysis propagates *values*;
  disable_timing disables a single arc. Don't mix on the same
  intention.
- **Mode-specific clock uncertainty forgotten.** Scan-mode uncertainty
  is usually smaller (slow clock, less jitter); reusing functional
  uncertainty over-margins scan.

## Citations

- **SDC 1.9** — `set_case_analysis`, `set_clock_groups`,
  `set_disable_timing`.
- **Gangadharan & Churiwala**, *Constraining Designs for Synthesis and
  Timing Analysis* (Springer 2013), Chapter 14.

## See also

- `false-paths-catalog.md` — Category 4 (multi-mode paths); how to
  false-path between modes in merged SDC.
- `clock-declarations.md` — multiple `create_clock` on the same port.
- `sta` skill `references/mmmc-corners.md` — modes × corners sign-off
  matrix.
- `dft-patterns` skill `references/scan-chains.md` — what the scan
  mode actually drives.
