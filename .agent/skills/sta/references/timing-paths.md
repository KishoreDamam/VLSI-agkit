# Timing Paths

> Startpoints, endpoints, the four path groups, launch/capture model, and the
> data/clock arrival decomposition every `report_timing` row is built from.

## Startpoints and endpoints

A **timing path** is a chain of combinational logic between a startpoint and
an endpoint. STA enumerates every such path and computes slack for each.

| | Startpoint | Endpoint |
|---|---|---|
| **Definition** | Source of data | Sink of data |
| **Sync** | Output pin of a register, latch, or input port | Data pin (D) of a register, latch, or output port |
| **Async** | `set` / `clear` / `preset` pins | Recovery / removal checked against clock |

Startpoints and endpoints are not "the registers" — they are the *pins*. A
flip-flop with a synchronous clear participates as both a startpoint (Q) and
an endpoint (D, and async clear if present).

## The four path groups

Every path falls into exactly one group. Tool reports separate WNS/TNS per
group for triage:

| Group | Startpoint | Endpoint | Constraint that bounds it |
|---|---|---|---|
| **reg → reg** | flop/latch Q | flop/latch D | `create_clock` period (internal) |
| **in → reg** | input port | flop/latch D | `set_input_delay` |
| **reg → out** | flop/latch Q | output port | `set_output_delay` |
| **in → out** | input port | output port | `set_max_delay` (or both above) |

Triage heuristic: if **reg → reg** dominates WNS, the problem is internal
logic / pipelining. If **in → reg** or **reg → out** dominates, the
problem is usually constraint values from the I/O budget, not RTL.

## Launch and capture

For a reg-to-reg path:

```
        +--------+        Logic         +--------+
clk --> | Launch | --Q---> ===========> | Capture |
        | Reg    |                      | Reg     |--> ...
        +--------+                      +--------+
            ^                               ^
            |                               |
     T_launch_clk_arrival           T_capture_clk_arrival
```

- **Launch edge**: clock edge that *fires* the source register. For setup,
  this is at the *current* cycle (T=0). For hold, also T=0 (same edge).
- **Capture edge**: clock edge that *latches* into the destination. For
  setup, this is one period later (T=T_period). For hold, the *same* edge
  as launch (T=0).
- **Skew** = T_capture_clk_arrival − T_launch_clk_arrival. Positive skew
  helps setup, hurts hold.

This is why hold is "edge-on-edge same cycle" and setup is "edge-on-edge
next cycle" — the same two physical edges, but in setup analysis the
capture edge is shifted by one period in the math.

## Path data and path clock

`report_timing` splits the slack calculation into two sub-paths:

1. **Data path** — combinational delay from launch reg's Q to capture reg's
   D, including the clock-to-Q delay of the launch reg.
2. **Clock path** — clock-network delay from the clock root to each
   register's CK pin. Two sub-paths: one to launch CK, one to capture CK.

The slack is the difference between the **clock path budget** and the
**data path requirement** (plus setup or hold time).

## Path types: `-path_type` in report_timing

| `-path_type` | What it shows |
|---|---|
| `short` (default) | Data path summary, one line per cell |
| `full` | Full data path, all cells, with arrival/required at each |
| `full_clock` | Adds the clock-network arrival at launch and capture CKs |
| `full_clock_expanded` | Expands the clock network into individual buffer cells |

For master-level debugging always use `-path_type full_clock_expanded` — it
shows you exactly where clock latency comes from and lets you spot a buffer
that's eating your skew budget.

## Special path types

- **Recovery / removal**: async set/clear deassertion vs clock edge.
  Recovery is setup-like (deassertion must be stable before clock).
  Removal is hold-like (deassertion must not change too soon after clock).
- **Clock-gating check**: when a gating cell sits in a clock path, STA
  checks setup/hold of the enable wrt the gated clock. `report_clock_gating_check`.
- **Min pulse width**: clock period vs internal cell min-pulse-width
  constraints — checked separately with `report_min_pulse_width`.
- **Async paths**: between clocks declared async via `set_clock_groups`.
  Not timed by setup/hold; need `set_max_delay -datapath_only` (CDC) or
  structural sync verified by a separate CDC tool.

## Why path enumeration explodes

A small ASIC has millions of paths. Tools prune aggressively:

- Only the **worst N** paths per endpoint are reported (`-max_paths N`).
- **Path-based analysis (PBA)** re-times only the top paths with reduced
  pessimism after **graph-based analysis (GBA)** identifies them. GBA is
  fast and pessimistic; PBA is slow and tight.

For sign-off, use `report_timing -pba_mode path` on the top critical paths
to recover the GBA pessimism before deciding a fix is needed.

## Path-group customization

You can create custom path groups for finer-grained triage:

```tcl
group_path -name CRITICAL_IO -from [get_ports data_in*]
group_path -name DDR_OUT     -to   [get_ports ddr_dq*]
```

Then `report_timing_summary` shows WNS/TNS per custom group. Useful when an
I/O interface has its own closure deadline separate from internal logic.

## See also

- `setup-hold-equations.md` — what the slack formula actually computes.
- `report-timing-deepdive.md` — reading the report line by line.
- `clock-uncertainty.md` — where uncertainty plugs into the equation.
