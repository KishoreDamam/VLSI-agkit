# UVM Phasing — Deep Dive

> Every UVM phase explained: build / run-time / clean-up. When to override,
> which direction it executes, and why "use only run_phase" is the default
> recommendation despite all the runtime sub-phases existing.

## Three phase groups

```
                                     ┌── pre_reset ──┐
build  →  connect  →  end_of_elab ─┤    reset       │  shutdown ──→ extract
                                     │   post_reset    │     ▲          ↓
                                     │  pre_configure  │     │       check
                                     │    configure    │     │          ↓
                                     │ post_configure  │     │       report
                                     │     pre_main    │     │          ↓
                                     │       main      │     │        final
                                     │    post_main    │     │
                                     │  pre_shutdown   │     │
                                     │    shutdown     │     │
                                     │  post_shutdown ─┘     │
                                     └─── run (full duration) ┘
   Build phases             Run-time phases (parallel)        Clean-up phases
   (functions, 0-time)      (tasks, real time)                 (functions)
```

| Group | Type | Direction | Purpose |
|---|---|---|---|
| Build | function | top-down (build), bottom-up (connect, end_of_elab) | Construct + wire the testbench |
| Run-time | task | all parallel | Consume time — drive, monitor, check |
| Clean-up | function | bottom-up | Collect results, report pass/fail |

## Build phases (functions — zero time)

### `build_phase`
**Top-down.** Construct components via the factory.

```systemverilog
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mon = my_monitor::type_id::create("mon", this);
    if (get_is_active() == UVM_ACTIVE) begin
        drv = my_driver::type_id::create("drv", this);
        sqr = my_sequencer::type_id::create("sqr", this);
    end
endfunction
```

Top-down so the parent can configure its children *before* the children's
build runs. Use `uvm_config_db::set` here to push config to children, then
the child's `build_phase` calls `uvm_config_db::get`.

### `connect_phase`
**Bottom-up.** Wire TLM ports between already-built components.

```systemverilog
function void connect_phase(uvm_phase phase);
    if (get_is_active() == UVM_ACTIVE)
        drv.seq_item_port.connect(sqr.seq_item_export);
    mon.ap.connect(scoreboard.actual_fifo.analysis_export);
endfunction
```

Never create components here — they all exist by now. Connection only.

### `end_of_elaboration_phase`
**Bottom-up.** Final tweaks before simulation starts. Examples:

- Adjust factory overrides one last time.
- Print the topology with `uvm_top.print_topology()`.
- Verify expected hierarchy via `find_first()`.

Most testbenches don't override this phase.

## Run-time phases (tasks — real time)

The `run_phase` is the original OVM-era catch-all. The 12 sub-phases
(`pre_reset` through `post_shutdown`) were added by Accellera for finer
control. **Critical**: `run_phase` and all 12 sub-phases execute *in
parallel* on the same component, not sequentially.

| Phase | Typical use | Cookbook recommendation |
|---|---|---|
| `run_phase` | Drivers, monitors — anything that lives the whole sim | **Use for transactors** |
| `pre_reset_phase` | Wait for power-good | Rarely used |
| `reset_phase` | Generate DUT reset; default interface state | Use in test for reset stimulus |
| `post_reset_phase` | Training, rate negotiation | Rarely used |
| `pre_configure_phase` | Late-binding config changes | Rarely used |
| `configure_phase` | Program DUT registers, memories | Use in test for register init |
| `post_configure_phase` | Wait for config to propagate | Rarely used |
| `pre_main_phase` | Wait for components to be ready | Rarely used |
| `main_phase` | Run the test stimulus | **Use in test for main sequences** |
| `post_main_phase` | Finalize main | Rarely used |
| `pre_shutdown_phase` | Buffer before shutdown | Rarely used |
| `shutdown_phase` | Drain DUT, read final status | Use in test for end-of-test reads |
| `post_shutdown_phase` | Final activities | Rarely used |

### The cookbook recommendation (memorize this)

> **Transactors (drivers, monitors, agents, scoreboards) implement only
> `run_phase`.** Tests use `reset_phase`, `configure_phase`, `main_phase`,
> and `shutdown_phase`. Avoid the pre/post variants unless a real need
> arises.

Why: more phases ≠ better. The sub-phases add objection complexity.
Most testbench logic naturally fits one of the four mainline phases.

### Phase objections — required

```systemverilog
task main_phase(uvm_phase phase);
    phase.raise_objection(this, "main_seq running");
    main_seq = my_main_seq::type_id::create("main_seq");
    main_seq.start(env.agent.sqr);
    #(10 * PERIOD);
    phase.drop_objection(this, "main_seq complete");
endtask
```

Without `raise_objection`, the phase ends immediately. See
`objections-deep-dive.md` for the full mechanics.

## Clean-up phases (functions)

### `extract_phase`
**Bottom-up.** Pull statistics from scoreboards and coverage collectors.

```systemverilog
function void extract_phase(uvm_phase phase);
    super.extract_phase(phase);
    n_mismatch = mismatch_q.size();
endfunction
```

### `check_phase`
**Bottom-up.** Verify expected end-of-test conditions.

```systemverilog
function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    if (n_mismatch != 0)
        `uvm_error("CHECK", $sformatf("%0d mismatches", n_mismatch))
    if (!expected_fifo.is_empty())
        `uvm_error("LEFTOVER", "expected_fifo not drained")
endfunction
```

### `report_phase`
**Bottom-up.** Print summary, write coverage report.

### `final_phase`
**Bottom-up.** Last chance. Rarely used.

## User-defined phases

Accellera allows adding custom phases. Use `uvm_phase_schedule` and
register the phase. **In practice, don't**: it makes the testbench less
portable, and the default schedule covers nearly every case.

## Phase jumping

`phase.jump(uvm_reset_phase::get())` lets the test jump back to an
earlier run-time phase. Useful for repeating reset / configuration
loops in a single simulation. Use cautiously — phase jumps confuse
debuggers and analysis logs.

## Domains

A "domain" is a set of components sharing a phase schedule. The default
domain `uvm_domain::get_uvm_domain()` is the global one. Multi-domain
designs use separate domains so that, e.g., the SPI agent's
`main_phase` ends independently of the APB agent's `main_phase`.

```systemverilog
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    spi_agent.set_domain(uvm_domain::get_common_domain());
    apb_agent.set_domain(uvm_domain::get_common_domain());
endfunction
```

Most testbenches stick with the single default domain.

## Common pitfalls

- **Sequence started in `build_phase`.** `build_phase` is a function —
  zero time — sequences won't run. Start sequences in `run_phase` or
  `main_phase`.
- **`super.<phase>_phase(phase)` missing.** UVM framework cleanup code
  lives in the base class. Always call `super`.
- **Configuring a child via `uvm_config_db` *after* the child's
  build_phase has fired.** Top-down means parent build runs first;
  config must be `set` before the child's `build_phase`, i.e., in the
  parent's own `build_phase` *before* the `create()` call for the
  child (the `set` itself is fine inside the parent build_phase since
  the child hasn't run yet — the framework calls them in order).
- **Both `run_phase` and `main_phase` override on the same component.**
  Allowed but confusing — both run in parallel. Pick one per component.
- **No objection in run_phase.** Simulation exits before any time
  elapses. Always raise an objection in any time-consuming phase you
  override.
- **Objection raised after `@(posedge clk)`.** There's a one-cycle
  window where the phase can end. Raise the objection first, then wait.

## Citations

- **Mentor Graphics UVM Cookbook**, *Phasing* chapter — phase descriptions,
  recommendations on which to use, parallel execution semantics.
- **Accellera UVM 1.2 §9.3** — phase ordering, schedule, domains.
- **Accellera UVM 1.2 §9.6** — objection mechanism.

## See also

- `objections-deep-dive.md` — what `raise_objection` / `drop_objection`
  actually do.
- `component-architecture.md` — build_phase + connect_phase examples.
- `messaging-and-debug.md` — `+UVM_PHASE_TRACE` plusarg for debugging
  phase transitions.
