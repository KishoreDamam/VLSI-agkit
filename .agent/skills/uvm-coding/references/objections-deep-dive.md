# Objections — Deep Dive

> The `uvm_objection` mechanism is the single most common source of UVM
> "my test hung" and "my test ended too early" bugs. This reference
> covers the mechanics: count propagation, drain-time, callbacks, and
> the rules that prevent the bugs.

## What objections are for

A `uvm_objection` is a shared counter between components and sequences.
Participants `raise` (increment) and `drop` (decrement) it. When the
counter goes from non-zero back to zero, an "all-dropped" event fires.

The UVM phasing mechanism uses an objection per run-time phase to know
when the phase can end. **Tests raise an objection at start of stimulus
and drop it when stimulus is complete**; the phase ends when every
participant has dropped.

> **Cookbook recommendation**: only use the *built-in* phase objections.
> Don't create your own `uvm_objection` instances — the propagation
> mechanics are subtle and the overhead is real.

## The two-counter model

Each component (or sequence) maintains two counters:

| Counter | Definition |
|---|---|
| **Source (explicit) count** | Number of objections this object raised itself |
| **Total (implicit) count** | This object's source count + sum of total counts of all children |

Raising an objection at `env.agent.sqr` updates:

```
env.agent.sqr  source=1, total=1
env.agent      source=0, total=1
env            source=0, total=1
uvm_top        source=0, total=1
```

Dropping reverses each step.

The phase ends when `uvm_top.total = 0`.

## API surface

### Raising
```systemverilog
phase.raise_objection(this, "starting main_seq");
// Defaults: count=1
// 'this' is the source object (the component or sequence)
```

### Dropping
```systemverilog
phase.drop_objection(this, "main_seq complete");
```

### Drain time
```systemverilog
phase.set_drain_time(this, 100ns);
```

After the last drop, the framework waits `drain_time` before checking
if total really reached zero. If a new raise occurs during the drain,
the all-dropped event aborts.

### Status / debug
```systemverilog
phase.get_objection_count(this);           // source count
phase.get_objection_total(this);           // total count
phase.get_drain_time(this);
phase.display_objections(this, 1);         // dump
```

## The phase-end algorithm (precise)

When `drop_objection` is called:

1. Decrement source count of the dropping object by `count`.
2. Decrement total count of the dropping object by `count`.
3. Call `dropped()` callback (if a component).
4. If total > 0 OR parent is null → done.
5. If total == 0:
   - Fork:
     - Wait drain_time.
     - Call `all_dropped()` task callback, wait for completion.
     - Adjust for any raises/drops during the drain.
     - If total now stays at 0, repeat from step 2 on parent.

This means: **the all-dropped propagation up the hierarchy is
sequential, gated by each level's drain_time and `all_dropped()`
callback.**

## Recommended pattern

```systemverilog
class my_test extends uvm_test;
    `uvm_component_utils(my_test)
    // ... env construction in build_phase ...

    task main_phase(uvm_phase phase);
        my_main_seq seq;
        phase.raise_objection(this, "starting main_seq");
        seq = my_main_seq::type_id::create("seq");
        seq.start(env.agent.sqr);
        #(10 * env.cfg.clock_period);
        phase.drop_objection(this, "main_seq complete");
    endtask
endclass
```

Rules:

1. **Test raises and drops.** Components do not raise objections
   in normal use — they just live their `run_phase` lifetime.
2. **Raise before any time-consuming statement.** A `@(posedge clk)`
   before the raise creates a 1-cycle window where the phase can end.
3. **Always provide a description string.** It shows up in
   `+UVM_OBJECTION_TRACE` logs and saves an hour of debug later.
4. **Use the default count = 1.** Higher counts complicate accounting.
5. **Drain time only at uvm_top or test.** Avoid spreading drains
   across every component.

## Callbacks — don't use them

UVM exposes three callbacks on `uvm_component`:

| Callback | When fired |
|---|---|
| `raised(uvm_objection obj, uvm_object source_obj, string description, int count)` | On every raise on this component or any descendant |
| `dropped(...)` | On every drop |
| `all_dropped(...) task` | When total reaches 0 |

> **Cookbook recommendation**: do not override these callbacks. They
> are called on *every* raise/drop in the subtree — heavy overhead, no
> useful purpose for typical testbenches.

## Sequence objections

Sequences can raise objections, but propagation goes through the
**sequencer** the sequence is running on, not through the sequence
hierarchy. A child sequence's raise reaches uvm_top via the sequencer.

**Virtual sequences** (whose `m_sequencer` is null) do **not propagate**
objections. If your virtual sequence raises, the objection is invisible
to the phase. Set `m_sequencer` before raising, or raise in the test
instead.

The cookbook's strong guidance: **don't raise objections inside
sequences**. Raise in the test (or top-level component) that started
the sequence. This keeps end-of-test logic in one place.

## Drain time vs explicit delay

Two ways to give the DUT time to flush after stimulus:

```systemverilog
// Pattern A — explicit delay
seq.start(sqr);
#(10 * period);
phase.drop_objection(this);

// Pattern B — drain_time
phase.set_drain_time(this, 10 * period);
seq.start(sqr);
phase.drop_objection(this);
// drain_time elapses after the drop before phase actually ends
```

Pattern A is more explicit. Pattern B works better when the test
doesn't directly start the sequence (e.g., reactive testbench). Pick
one per testbench — don't mix.

## Phase-ready-to-end hook

Sometimes the test wants to extend the phase based on a runtime
condition (e.g., wait for a queue to drain). The
`phase_ready_to_end()` virtual function fires when the phase is about
to end:

```systemverilog
function void phase_ready_to_end(uvm_phase phase);
    if (!response_q.empty()) begin
        phase.raise_objection(this);
        fork begin
            wait (response_q.empty());
            phase.drop_objection(this);
        end join_none
    end
endfunction
```

This is the recommended end-of-test extension mechanism (cookbook §8.1).

## Common pitfalls

| Bug | Cause |
|---|---|
| "Simulation ends immediately" | No objection raised in time-consuming phase |
| "Simulation hangs forever" | Objection raised, never dropped (e.g., exception in body before drop) |
| "Test passes but no stimulus ran" | Objection raised by sequence with null sequencer — never propagated |
| "Phase ends right after starting" | Raise was after `@(posedge clk)` — 1-cycle window |
| "All_dropped fires repeatedly" | Components raising and dropping inside scoreboard `forever` loop |

### Defensive pattern — wrap in try/finally-style

```systemverilog
task main_phase(uvm_phase phase);
    phase.raise_objection(this);
    begin
        // any cleanup needed even on early exit
        seq.start(sqr);
    end
    phase.drop_objection(this);
endtask
```

SV doesn't have try/finally; structure the code so the drop is the
last statement. If the sequence can fail, use a fork/join pattern with
a watchdog so the drop always runs.

## Debug

```bash
# Trace every raise/drop with timestamps and sources
vsim +UVM_OBJECTION_TRACE +UVM_PHASE_TRACE -uvmcontrol=all

# In code, dump current state
phase.display_objections(this, 1);
```

`+UVM_OBJECTION_TRACE` is invaluable when "the test ends 1 ns too
early" or "the test never ends." It prints every raise and drop with
the description string. See `messaging-and-debug.md`.

## Citations

- **Mentor Graphics UVM Cookbook**, *Objections* chapter — mechanics,
  callback recommendations, hierarchy propagation, drain time.
- **Accellera UVM 1.2 §9.6** — objection API.
- **Cookbook §8.1, 8.2** — end-of-test rules: use objections; don't
  raise per-transaction.

## See also

- `phasing-deep-dive.md` — when each phase's objection matters.
- `sequences-and-items.md` — sequence vs sequencer for objection
  propagation.
- `messaging-and-debug.md` — `+UVM_OBJECTION_TRACE` and friends.
