# false_path vs set_max_delay -datapath_only

Choosing the right SDC constraint for CDC paths is a correctness decision,
not a style preference. The wrong choice either leaves timing unverified or
causes overconstraint.

---

## Summary Table

| Constraint | What the tool does | Risk | When to use |
|---|---|---|---|
| `set_false_path` | Removes path from timing analysis entirely | Router may use an unboundedly long path; metastability window not closed | 2-FF synchronizer control signal if you fully trust synchronizer placement; reset assertion path |
| `set_max_delay -datapath_only` | Bounds combinational delay, excludes clock skew | Slightly more conservative (adds setup/hold from source clock) | FIFO gray pointers, handshake data buses, any path where arrival time matters |

---

## false_path — Full Explanation

```tcl
set_false_path -from [get_clocks clk_src] -to [get_clocks clk_dst]
```

The timing analyzer **removes** all paths between the two clock domains from
its analysis. This means:

- **No setup/hold check** on the receiving FF.
- **No maximum delay check** on the combinational path.
- The router is free to use any routing resource, including long paths that
  could push the data arrival past the metastability window.

**When this is acceptable:**
- The synchronizer itself guarantees metastability handling (2FF/3FF), AND
- You have synthesis constraints (`dont_touch`, `ASYNC_REG`) that force the
  synchronizer FFs to be placed adjacent so routing is minimal, AND
- You only need to suppress noise from the timing tool, not bound the path.

**When this is not acceptable:**
- Multi-bit data buses crossing domains (bit skew could cause transient wrong values)
- Gray pointer paths in async FIFOs (must arrive within destination period)
- Handshake data buses (must arrive before destination samples)

---

## set_max_delay -datapath_only — Full Explanation

```tcl
set_max_delay <T_dst> -datapath_only \
    -from [get_cells *src_reg*] \
    -to   [get_cells *sync_pipe[0]*]
```

The timing analyzer:

1. **Checks** that the combinational path from source FF output to destination
   FF input completes within `<T_dst>`.
2. **Excludes clock skew** (`-datapath_only`) — meaningful because src and dst
   clocks are asynchronous and have no defined phase relationship.
3. **Does not check** hold time against src clock (correct for CDC).

**Choosing the bound:**
- Set to ≤ destination clock period for synchronizer first-stage paths.
- For FIFO gray pointers: use the destination period (ensures data arrives
  before the first destination rising edge after it was launched).
- For handshake data buses: use the destination period; the protocol guarantees
  stability for much longer, so this is conservative and safe.

---

## Decision Flowchart

```
Is the path a synchronizer control signal (1-bit, synchronizer handles metastability)?
  └─ YES: set_false_path is acceptable IF you have ASYNC_REG/dont_touch placement
  └─ NO:
      Is it a data bus, FIFO pointer, or handshake data?
        └─ YES: set_max_delay -datapath_only ≤ T_dst
        └─ NO (reset assert path): set_false_path -to [first FF D pin]
```

---

## Example: Async FIFO Gray Pointer (100 MHz wr / 250 MHz rd)

```tcl
create_clock -name wr_clk -period 10.0 [get_ports wr_clk]
create_clock -name rd_clk -period  4.0 [get_ports rd_clk]

# Declare asynchronous — suppresses impossible inter-domain path reports
set_clock_groups -asynchronous -group {wr_clk} -group {rd_clk}

# Bound wr→rd gray pointer path to rd clock period (4 ns)
set_max_delay 4.0 -datapath_only \
    -from [get_cells -hier -filter {NAME =~ *wr_ptr_gray_reg*}] \
    -to   [get_cells -hier -filter {NAME =~ *u_sync_wr2rd/pipe[0]*}]

# Bound rd→wr gray pointer path to wr clock period (10 ns)
set_max_delay 10.0 -datapath_only \
    -from [get_cells -hier -filter {NAME =~ *rd_ptr_gray_reg*}] \
    -to   [get_cells -hier -filter {NAME =~ *u_sync_rd2wr/pipe[0]*}]
```

Using `set_false_path` here instead would allow the router to use a 20 ns
routing detour on the wr→rd path, meaning the data could arrive more than
4 ns after launch — the synchronizer's first FF would see a glitch or stale
value, exactly the race condition async FIFOs are designed to prevent.

---

## Citation

The `-datapath_only` flag behavior is defined in the SDC 1.9 standard
(Synopsys SDC Reference Manual) and implemented identically in Vivado Tcl
and Cadence Innovus. The flag was introduced specifically for CDC constraints
where clock-skew analysis is meaningless.
