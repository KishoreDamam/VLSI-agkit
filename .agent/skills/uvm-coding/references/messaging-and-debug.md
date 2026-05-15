# UVM Messaging & Debug

> Verbosity, message IDs, plusarg controls, and the built-in debug
> dumps (factory / config_db / phasing / objections / TLM ports / callbacks).
> Run-time controls that don't require recompiling the testbench.

## The four severities

| Macro | Behavior on default sim |
|---|---|
| `` `uvm_info(ID, MSG, V) `` | Logged at verbosity V; default verbosity is UVM_MEDIUM |
| `` `uvm_warning(ID, MSG) `` | Logged, simulation continues |
| `` `uvm_error(ID, MSG) `` | Logged, error count incremented, simulation continues by default |
| `` `uvm_fatal(ID, MSG) `` | Logged and `$finish` called |

```systemverilog
`uvm_info  ("AXI_DRV", "starting write burst", UVM_MEDIUM)
`uvm_warning("AXI_DRV", "unexpected B-channel id mismatch")
`uvm_error  ("AXI_DRV", $sformatf("RRESP=%0d", rresp))
`uvm_fatal  ("AXI_DRV", "DUT did not respond to reset")
```

Use these **macros**, not the free functions like `uvm_report_info`.
The macros route through `this.uvm_report_info()` so per-component
verbosity/severity overrides take effect.

## Verbosity levels

| Level | Numeric | Use |
|---|---|---|
| UVM_NONE | 0 | Always print (error/fatal level) |
| UVM_LOW | 100 | Major events (config done, test start) |
| UVM_MEDIUM | 200 | Normal info — default print threshold |
| UVM_HIGH | 300 | Per-transaction info |
| UVM_FULL | 400 | Every signal-level detail |
| UVM_DEBUG | 500 | Anything else |

Message is printed if `verbosity_level <= component_verbosity`. By
default the threshold is UVM_MEDIUM, so `UVM_HIGH`/`UVM_FULL` messages
are suppressed.

## Global controls — `+UVM_*` plusargs

Set on the simulator command line, no recompile:

| Plusarg | Effect |
|---|---|
| `+UVM_TESTNAME=<class>` | Pick the `uvm_test` to run |
| `+UVM_VERBOSITY=<level>` | Global verbosity threshold |
| `+UVM_TIMEOUT=<time>` | Global hard timeout (e.g., `+UVM_TIMEOUT=10ms`) |
| `+UVM_MAX_QUIT_COUNT=<n>` | Stop after N errors |
| `+UVM_OBJECTION_TRACE` | Log every raise/drop with source + description |
| `+UVM_PHASE_TRACE` | Log every phase entry/exit |
| `+UVM_CONFIG_DB_TRACE` | Log every config_db set/get |
| `+UVM_RESOURCE_DB_TRACE` | Log every resource_db access |
| `+UVM_FACTORY_TRACE` | Log every factory create/override |
| `+UVM_TR_RECORD` | Enable transaction recording |
| `+uvm_set_verbosity=<path>,<id>,<level>,<phase>` | Per-component override (see below) |
| `+uvm_set_action=<path>,<id>,<sev>,<action>` | Per-message action (downgrade error→info etc) |
| `+uvm_set_severity=<path>,<id>,<orig>,<new>` | Change severity at runtime |

Examples:

```bash
# Run a specific test at higher verbosity
vsim tb_top +UVM_TESTNAME=my_smoke_test +UVM_VERBOSITY=UVM_HIGH

# Debug phase / objection issues
vsim tb_top +UVM_TESTNAME=my_test +UVM_OBJECTION_TRACE +UVM_PHASE_TRACE

# Trace config_db at startup
vsim tb_top +UVM_TESTNAME=my_test +UVM_CONFIG_DB_TRACE

# Downgrade a known false-positive error to warning at runtime
vsim tb_top +UVM_TESTNAME=my_test \
    +uvm_set_action="*,RACE_MISMATCH,UVM_ERROR,UVM_DISPLAY|UVM_NO_ACTION"

# Increase verbosity only on one component
vsim tb_top +UVM_TESTNAME=my_test \
    +uvm_set_verbosity="uvm_test_top.env.agent.drv,_ALL_,UVM_FULL,run"
```

## Fine-grained verbosity control (in code)

```systemverilog
// In a test or env build_phase:
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Lower verbosity on a noisy component
    set_report_verbosity_level_hier(UVM_LOW);
    env.agent.drv.set_report_id_verbosity("AXI_DRV", UVM_FULL);
endfunction
```

Methods:

- `set_report_verbosity_level(V)` — this component only.
- `set_report_verbosity_level_hier(V)` — this and descendants.
- `set_report_id_verbosity(ID, V)` — only messages with that ID.
- `set_report_severity_action(SEV, A)` — what to do on each severity.

## Message ID conventions

The cookbook recommends a stable, greppable ID:

| Prefix | Component |
|---|---|
| `AXI_DRV` | AXI driver |
| `AXI_MON` | AXI monitor |
| `SB_CFG` | Scoreboard config |
| `RAL_ADP` | RAL adapter |
| `VSEQ_CHIP_INIT` | Specific virtual sequence |

Don't use `"INFO"`, `"DEBUG"`, `"ERROR"` as IDs — they don't filter well.
Don't include dynamic data in the ID — that's the message field's job.

## Debug dumps

### Factory contents

```systemverilog
function void start_of_simulation_phase(uvm_phase phase);
    factory.print();                          // every registered type + overrides
endfunction
```

Or on the command line: `+UVM_FACTORY_TRACE` logs each `type_id::create`
and override.

### config_db contents

```systemverilog
uvm_config_db_options::turn_on_tracing();      // before run_test
uvm_resource_db::dump();                       // dump entire resource db
```

Or `+UVM_CONFIG_DB_TRACE +UVM_RESOURCE_DB_TRACE` on the command line.

### Component topology

```systemverilog
function void start_of_simulation_phase(uvm_phase phase);
    super.start_of_simulation_phase(phase);
    uvm_top.print_topology();
endfunction
```

Prints the entire UVM component tree with types, instance names, and
port connections.

### Phase trace

```bash
vsim tb_top +UVM_TESTNAME=my_test +UVM_PHASE_TRACE
```

Logs each phase entry/exit with timestamp. Essential when "the test
hangs in phase X" — shows you exactly which phase isn't ending.

### Objection trace

```bash
vsim tb_top +UVM_TESTNAME=my_test +UVM_OBJECTION_TRACE
```

Logs every raise and drop with source object + description. See
`objections-deep-dive.md`.

### TLM port debug

```systemverilog
// Show all port/export connections at end_of_elaboration
function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    uvm_top.print_topology();
endfunction
```

`uvm_tlm_analysis_fifo`'s `is_empty()`, `size()`, `used()` methods help
in `check_phase`:

```systemverilog
function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    if (!expected_fifo.is_empty())
        `uvm_error("LEFTOVER",
            $sformatf("expected_fifo has %0d items at end-of-test",
                      expected_fifo.size()))
endfunction
```

## Performance considerations

`` `uvm_info `` is **not free**, even when filtered out. The macro
expands to:

```systemverilog
if (uvm_report_enabled(VERB, UVM_INFO, ID)) `uvm_info_context(...)
```

— a function call per attempt. Inside a `forever` loop running every
cycle, even filtered `` `uvm_info `` adds simulation overhead.

For ultra-hot paths, wrap the call:

```systemverilog
if (verbose) `uvm_info("HOT", $sformatf("..."), UVM_HIGH)
```

…and toggle `verbose` at runtime via a config flag.

## Recommended logging pattern

```systemverilog
class my_driver extends uvm_driver #(my_item);
    `uvm_component_utils(my_driver)

    task run_phase(uvm_phase phase);
        my_item item;
        `uvm_info("DRV", "starting run_phase", UVM_LOW)
        forever begin
            seq_item_port.get_next_item(item);
            `uvm_info("DRV", $sformatf("got item: %s",
                                        item.convert2string()),
                       UVM_HIGH)
            drive(item);
            seq_item_port.item_done();
        end
    endtask
endclass
```

Pattern:
- `UVM_LOW` for one-shot lifecycle events.
- `UVM_MEDIUM` for major state changes.
- `UVM_HIGH` for per-transaction.
- `UVM_FULL` for sub-transaction signal-level detail.

## Common pitfalls

- **Using `$display` / `$write` instead of `` `uvm_info ``.** Bypasses
  the report system; no verbosity/severity controls; no per-component
  filtering.
- **Hardcoding verbosity levels in code.** Use command-line plusargs;
  don't recompile to change debug noise.
- **Generic message IDs.** "`DEBUG`" or "`MSG`" is unfilterable. Always
  prefix-by-component.
- **Computing the message string before the verbosity check.**
  `` `uvm_info(ID, $sformatf("expensive: %s", to_string(big_obj)), UVM_HIGH) ``
  computes the string even when filtered. For expensive strings, wrap
  in `if (uvm_report_enabled(UVM_HIGH, UVM_INFO, "ID"))`.
- **Using the `_context` variants without a context.** `` `uvm_info_context ``
  takes a component handle — needed when reporting from sequences or
  from a non-component scope. Plain `` `uvm_info `` works inside a
  component method.
- **Ignoring `+UVM_OBJECTION_TRACE` output as "noise".** It's the
  fastest way to debug end-of-test issues.

## Citations

- **Mentor Graphics UVM Cookbook**, *Messaging* / *Debug Features* — verbosity,
  plusargs, component-level filtering, debug dumps.
- **Accellera UVM 1.2 §6** — report mechanism, `uvm_report_handler`.

## See also

- `objections-deep-dive.md` — `+UVM_OBJECTION_TRACE` for end-of-test
  debugging.
- `phasing-deep-dive.md` — `+UVM_PHASE_TRACE` for phase debugging.
- `component-architecture.md` — `+UVM_CONFIG_DB_TRACE` for config debugging.
