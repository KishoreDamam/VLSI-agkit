# UVM Component Architecture

> Factory registration, config_db, active/passive agents, and phase ordering.

## UVM component hierarchy

```
uvm_top (implicit root)
  └─ test (uvm_test)
       └─ env (uvm_env)
            ├─ agent (uvm_agent)
            │    ├─ sequencer (uvm_sequencer)
            │    ├─ driver    (uvm_driver)       ← active mode only
            │    └─ monitor   (uvm_monitor)
            ├─ scoreboard (uvm_scoreboard)
            └─ coverage   (uvm_subscriber)
```

TLM connections (set up in `connect_phase`):
```
sequencer.seq_item_export ←── driver.seq_item_port
monitor.ap ──→ scoreboard.actual_fifo.analysis_export
monitor.ap ──→ coverage.analysis_export
```

---

## Factory registration: `uvm_component_utils` vs `uvm_object_utils`

| Macro | Applies to | Constructor signature |
|---|---|---|
| `` `uvm_component_utils(T) `` | `uvm_component` subclasses (agents, drivers, monitors, scoreboards, envs, tests) | `new(string name, uvm_component parent)` |
| `` `uvm_object_utils(T) `` | `uvm_object` subclasses (sequence items, sequences, config objects, transactions) | `new(string name = "T")` |

**Rule:** if it has a `parent` argument, use `uvm_component_utils`. If it is allocated and cloned (randomized), use `uvm_object_utils`.

```systemverilog
class my_config extends uvm_object;      // no parent — uvm_object
    `uvm_object_utils(my_config)
    uvm_active_passive_enum is_active = UVM_ACTIVE;
    function new(string name = "my_config"); super.new(name); endfunction
endclass

class my_driver extends uvm_driver #(my_item);  // has parent — uvm_component
    `uvm_component_utils(my_driver)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
endclass
```

---

## Phase ordering

### build_phase — top-down (parent before child)

The framework calls `build_phase` on parent before children. This means the parent must
create children with `type_id::create` so children exist before the framework calls their
own `build_phase`.

```systemverilog
function void build_phase(uvm_phase phase);
    super.build_phase(phase);  // always call super first
    monitor = my_monitor::type_id::create("monitor", this);
    if (get_is_active() == UVM_ACTIVE) begin
        driver    = my_driver::type_id::create("driver", this);
        sequencer = my_sequencer::type_id::create("sequencer", this);
    end
endfunction
```

### connect_phase — bottom-up (child before parent)

The framework calls `connect_phase` on children before parents. Wire TLM ports here.

```systemverilog
function void connect_phase(uvm_phase phase);
    if (get_is_active() == UVM_ACTIVE)
        driver.seq_item_port.connect(sequencer.seq_item_export);
    monitor.ap.connect(scoreboard.actual_fifo.analysis_export);
endfunction
```

**Never create new objects in `connect_phase`** — all components must exist at this point.

---

## Active vs passive agent

```systemverilog
class my_agent extends uvm_agent;
    `uvm_component_utils(my_agent)

    my_driver    drv;
    my_sequencer sqr;
    my_monitor   mon;

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        mon = my_monitor::type_id::create("mon", this);  // always created
        if (get_is_active() == UVM_ACTIVE) begin          // driver+sqr only when active
            drv = my_driver::type_id::create("drv", this);
            sqr = my_sequencer::type_id::create("sqr", this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        if (get_is_active() == UVM_ACTIVE)
            drv.seq_item_port.connect(sqr.seq_item_export);
    endfunction
endclass
```

Set active/passive at the top level before `build_phase` fires:
```systemverilog
// In test or env build_phase:
uvm_config_db #(uvm_active_passive_enum)::set(
    this, "env.agent", "is_active", UVM_PASSIVE);
```

---

## `uvm_config_db` set/get pattern

### Set (top level — test or module)
```systemverilog
// In top-level testbench module:
initial begin
    uvm_config_db #(virtual axi_lite_if)::set(
        null,          // context: null = uvm_top
        "uvm_test_top.env.agent.*",  // path: wildcard matches drv and mon
        "vif",         // field name
        u_axi_if       // value: the interface instance
    );
    run_test("axi_base_test");
end
```

### Get (in component build_phase)
```systemverilog
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(virtual axi_lite_if)::get(
            this, "", "vif", vif))
        `uvm_fatal("NOVIF", {"VIF not set for ", get_full_name()})
endfunction
```

**Common mistake:** the context string in `set` must match the component's `get_full_name()`.
Using `"*"` as path is safe but can cause multiple matches in large envs; be specific in
production code.

---

## Phase objection protocol

```systemverilog
task run_phase(uvm_phase phase);
    phase.raise_objection(this, "starting main_seq");
    main_seq = my_seq::type_id::create("main_seq");
    main_seq.start(env.agent.sqr);       // blocking
    #(10 * PERIOD);                       // drain: let DUT flush pipeline
    phase.drop_objection(this, "main_seq done");
endtask
```

**Rules:**
- Raise objection **before** the first `@(...)` or time-consuming call.
- Drop objection after all stimulus is complete and DUT has drained.
- Only one component needs to raise/drop (typically the test); others can observe.
- `set_drain_time(this, 100ns)` is an alternative to the explicit `#delay` before drop.

**Pitfall:** If `raise_objection` is called after a `@(posedge clk)`, there is a one-cycle
window where the phase can end if no other objection is active.
