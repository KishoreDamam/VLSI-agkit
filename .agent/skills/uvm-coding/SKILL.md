---
name: uvm-coding
description: Use when building a UVM testbench — writing sequence items with constraints, sequences/drivers/monitors, scoreboards with TLM analysis ports and dual FIFOs, the register layer (RAL), or wiring up UVM phases.
---

# UVM Coding Patterns

> Production-grade UVM 1.2 patterns for SystemVerilog testbenches: factory, config_db, TLM, sequences, and phasing.

## When to use

- You are writing a new UVM agent (driver, monitor, sequencer) from scratch.
- You need to wire analysis ports between a monitor, scoreboard, and coverage collector.
- You are implementing a sequence with randomized constraints and need the `uvm_do_with` idiom.
- You are debugging a sequence that stalls, a scoreboard that misses transactions, or a simulation that never ends.
- You need to integrate UVM RAL (register abstraction layer) with a bus adapter.
- You are deciding which UVM phase to create vs configure vs start stimulus in.

## Quick reference

| Pattern | Use when | Anti-pattern |
|---|---|---|
| `` `uvm_object_utils(T) `` | sequence items, sequences, config objects | Direct `new()` without factory registration |
| `` `uvm_component_utils(T) `` | drivers, monitors, agents, scoreboards | `` `uvm_object_utils `` on components (no parent arg) |
| `T::type_id::create("name", parent)` | instantiating any UVM class | `new("name", parent)` — bypasses factory overrides |
| `uvm_config_db#(T)::set/get` | passing VIF, config objects down hierarchy | Module-level global variables for interface handles |
| `phase.raise_objection` / `phase.drop_objection` | preventing run_phase from ending | No objection → simulation ends immediately |
| `analysis_port.connect(analysis_export)` | wiring monitor to scoreboard/coverage | Connecting export→port (reversed — UVM fatal at end_of_elaboration) |
| `uvm_tlm_analysis_fifo` | decoupling monitor write rate from scoreboard | Raw `q[$]` on scoreboard — blocks zero-time `write()` callers and has no per-item get() |

## Core patterns

### 1. Sequence item with constraints

**Use when:** defining the transaction type passed between sequences and drivers.

```systemverilog
class axi_seq_item extends uvm_sequence_item;
    `uvm_object_utils(axi_seq_item)

    rand logic [31:0] addr;
    rand logic [31:0] data;
    rand logic        we;

    // AXI-Lite: 4-byte aligned, lower 16-bit address space
    constraint c_align  { addr[1:0] == 2'b00; }
    constraint c_range  { addr inside {[32'h0000_0000 : 32'h0000_FFFC]}; }

    function new(string name = "axi_seq_item");
        super.new(name);
    endfunction

    function string convert2string();
        return $sformatf("addr=0x%08h data=0x%08h %s",
                         addr, data, we ? "WR" : "RD");
    endfunction
endclass
```

- **Gotchas:** `convert2string` is required for `uvm_info` and comparator error messages. Always implement it.
- Always check `randomize()` return value — never ignore it silently.

> Full item with `do_copy`/`do_compare`: `references/sequences-and-items.md`.

---

### 2. Sequence with `uvm_do_with`

**Use when:** sending constrained-random transactions from a sequence body.

```systemverilog
class axi_write_seq extends uvm_sequence #(axi_seq_item);
    `uvm_object_utils(axi_write_seq)

    int unsigned count = 8;

    function new(string name = "axi_write_seq");
        super.new(name);
    endfunction

    task body();
        repeat (count) begin
            // uvm_do_with: alloc + randomize with inline constraint + send
            `uvm_do_with(req, { we == 1'b1; addr < 32'h0100; })
        end
    endtask
endclass
```

- **Gotchas:** Some tools have limited support for `` `uvm_do_with ``. Use the explicit form if needed:
  ```systemverilog
  req = axi_seq_item::type_id::create("req");
  start_item(req);
  if (!req.randomize() with { we == 1'b1; }) `uvm_fatal("RAND", "randomize failed")
  finish_item(req);
  ```
- `start_item`/`finish_item` is the underlying mechanism; `uvm_do*` macros expand to this.

> Virtual sequences, p_sequencer, arbitration modes: `references/sequences-and-items.md`.

---

### 3. Driver + Monitor pair

**Use when:** building an agent for a new bus protocol.

**Driver:**

```systemverilog
class axi_driver extends uvm_driver #(axi_seq_item);
    `uvm_component_utils(axi_driver)
    virtual axi_lite_if vif;
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db #(virtual axi_lite_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "axi_lite_if vif not found in config_db")
    endfunction
    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);  // blocks until sequence sends item
            drive_txn(req);
            seq_item_port.item_done();          // MUST call — releases sequence
        end
    endtask
    task drive_txn(axi_seq_item item); /* protocol-specific */ endtask
endclass
```

**Monitor:**

```systemverilog
class axi_monitor extends uvm_monitor;
    `uvm_component_utils(axi_monitor)
    virtual axi_lite_if vif;
    uvm_analysis_port #(axi_seq_item) ap;  // wire to scoreboard/coverage
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ap = new("ap", this);  // TLM ports use new() — not factory-registered
        if (!uvm_config_db #(virtual axi_lite_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "axi_lite_if vif not found in config_db")
    endfunction
    task run_phase(uvm_phase phase);
        forever begin
            axi_seq_item item;
            @(posedge vif.clk iff (vif.awvalid && vif.awready));
            item = axi_seq_item::type_id::create("mon_item");
            item.addr = vif.awaddr; item.data = vif.wdata; item.we = 1'b1;
            ap.write(item);   // broadcast to all connected exports
        end
    endtask
endclass
```

- **Gotchas:** `item_done()` is mandatory after `get_next_item()`. Forgetting it stalls the sequence permanently with no error message.
- `uvm_analysis_port` uses `new()` because TLM ports are not factory-registered (`uvm_component_utils` is never applied to ports); `type_id::create()` does not exist for them.

> Agent active/passive mode, config_db hierarchy: `references/component-architecture.md`.

---

### 4. Scoreboard with dual TLM FIFOs

**Use when:** comparing an expected stream (from reference model) against an actual stream (from monitor).

```systemverilog
class axi_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(axi_scoreboard)

    uvm_tlm_analysis_fifo #(axi_seq_item) expected_fifo;
    uvm_tlm_analysis_fifo #(axi_seq_item) actual_fifo;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        expected_fifo = new("expected_fifo", this);
        actual_fifo   = new("actual_fifo",   this);
    endfunction

    // Caller (env): ref_model.ap.connect(sb.expected_fifo.analysis_export)
    //               monitor.ap.connect(sb.actual_fifo.analysis_export)

    task run_phase(uvm_phase phase);
        axi_seq_item exp_item, act_item;
        forever begin
            expected_fifo.get(exp_item);  // blocks until item available
            actual_fifo.get(act_item);
            if (exp_item.data !== act_item.data)
                `uvm_error("MISMATCH", $sformatf(
                    "Expected: %s  Actual: %s",
                    exp_item.convert2string(), act_item.convert2string()))
        end
    endtask
endclass
```

- **Gotchas:** The FIFO's `analysis_export` is the connection target, not the FIFO itself.
- The scoreboard does NOT raise an objection — the test owns raise/drop. If the scoreboard raised its own and the `forever` loop never exited, simulation would deadlock.
- Built-in alternative: `uvm_in_order_comparator #(T)` handles dual-FIFO logic automatically.

> Full analysis port topology, `uvm_subscriber`, coverage: `references/analysis-ports-and-scoreboards.md`.

---

### 5. UVM phases — where to put what

**Use when:** deciding which phase callback to override for a given action.

| Phase | Direction | What to do here |
|---|---|---|
| `build_phase` | Top-down | `type_id::create` components; `config_db::get` objects |
| `connect_phase` | Bottom-up | `port.connect(export)`; never create objects here |
| `start_of_simulation_phase` | Bottom-up | Print topology with `uvm_top.print_topology` |
| `run_phase` | Parallel | Raise objection; start sequences; drive and monitor |
| `check_phase` | Bottom-up | Verify FIFO emptiness, counters, error counts |
| `report_phase` | Bottom-up | Print summary statistics |

```systemverilog
task run_phase(uvm_phase phase);
    phase.raise_objection(this);           // prevent premature exit
    main_seq.start(env.agent.sequencer);   // blocking — runs entire sequence
    #100ns;                                // optional drain time
    phase.drop_objection(this);            // allow simulation to end
endtask
```

- **Key rule:** Never start a sequence or drive an interface in `build_phase`. The DUT elaboration completes before `run_phase`; driving in `build_phase` is a zero-time function call — no stimulus occurs.
- Objection must be raised before the first time-consuming operation.

> Phase scheduling details, drain time: `references/component-architecture.md`.

---

## Anti-patterns (do NOT do this)

1. **`randomize()` return value ignored** — returns 0 on constraint conflict; silently produces out-of-constraint data. Always: `assert(item.randomize() with {...}) else \`uvm_fatal(...)`.
2. **Missing `item_done()` in driver** — the sequencer holds `get_next_item()` waiting for `item_done()`; the sequence stalls forever with no timeout or error.
3. **`` `uvm_report_* `` free functions instead of `` `uvm_info/error `` macros** — free functions bypass the component's report handler, losing per-component verbosity filtering and severity overrides; `` `uvm_info `` routes through `this.uvm_report_info()` so component-level controls apply.
4. **Virtual interface handle set in interface declaration, not config_db** — hardcoding `virtual my_if vif = dut.intf` couples the testbench to one DUT hierarchy path; use `uvm_config_db` so the binding is set at the top level and overridable per test.
5. **Sequences started in `build_phase`** — sequences require a live sequencer and simulation time; `build_phase` is a void function (zero-time); calling `seq.start()` there is a phase-ordering violation.
6. **`new()` instead of `type_id::create()` for UVM components** — bypasses the factory; test overrides have no effect.
7. **`analysis_port.connect(analysis_port)`** — ports connect TO exports: `producer_port.connect(consumer_export)`.
8. **No objection raised in `run_phase`** — simulation exits before any stimulus runs.

---

## Validation checklist

- [ ] Every `uvm_component` subclass uses `` `uvm_component_utils ``; every `uvm_object` subclass uses `` `uvm_object_utils ``.
- [ ] All UVM components created with `type_id::create("name", parent)` — no bare `new()` for components.
- [ ] `convert2string()` implemented on every sequence item class.
- [ ] Driver `run_phase` loop: `get_next_item` then drive then `item_done` — every iteration.
- [ ] `uvm_config_db::get` for virtual interface is checked with `` `uvm_fatal `` on failure.
- [ ] Analysis port connections go port→export (`monitor.ap.connect(sb.fifo.analysis_export)`).
- [ ] `run_phase` raises objection before first `@` delay and drops it after last stimulus.
- [ ] All `randomize()` calls guarded with `assert(... .randomize() with {...})`.
- [ ] No sequences started in `build_phase` or `connect_phase`.
- [ ] Active vs passive agent guarded with `if (get_is_active() == UVM_ACTIVE)` in `build_phase`.

---

## Citations

- Accellera UVM 1.2 Reference (2014) §5.3 — `uvm_component_utils` factory registration.
- Accellera UVM 1.2 Reference §14.2 — `uvm_config_db` set/get semantics and context string matching.
- Accellera UVM 1.2 Reference §12.1 — sequence item lifecycle: `start_item`/`finish_item`.
- Accellera UVM 1.2 Reference §9.3 — phase ordering: top-down build, bottom-up connect.
- Accellera UVM 1.2 Reference §9.6 — objection mechanism and drain time.
- Accellera UVM 1.2 Reference §10.6 — `uvm_tlm_analysis_fifo` thread-safe FIFO adapter.

---

## See also

**Core architecture:**
- `references/component-architecture.md` — factory + overrides catalog, config_db precedence, virtual-interface package pattern, dual-top, active/passive agent, build/connect ordering
- `references/uvm-package-structure.md` — five-tier package hierarchy (utility/agent/sequence/env/test), directory layout, file naming, namespace hygiene

**Phasing & objections:**
- `references/phasing-deep-dive.md` — every build / run-time / cleanup phase, when to use each, parallel run-time phase execution
- `references/objections-deep-dive.md` — raise/drop mechanics, count propagation, drain time, `phase_ready_to_end`, callbacks (don't use them)

**Stimulus:**
- `references/sequences-and-items.md` — body idioms, late randomization, polymorphism, sequence library, arbitration, pipelined drivers, slave drivers
- `references/virtual-sequences-and-layering.md` — virtual sequencer + sequence, translator sequences, API/worker/virtual hierarchy

**Analysis:**
- `references/analysis-ports-and-scoreboards.md` — monitor anatomy, predictor (proxy DUT), dual-FIFO scoreboard, `uvm_subscriber`, post-run phases

**Register layer:**
- `references/register-model.md` — building the model, adapter, predictor (auto vs passive), access methods, built-in sequences, backdoor HDL paths, quirky-register callbacks, RAL-driven scoreboard + coverage

**Operations:**
- `references/messaging-and-debug.md` — verbosity, message IDs, plusargs (`+UVM_OBJECTION_TRACE` etc.), factory / config_db / phase / TLM-port debug dumps
- `references/two-kingdoms-emulation.md` — HDL-domain vs testbench-domain split for emulation-ready BFM-based testbenches

**Examples:**
- `examples/axi_lite_agent.sv` — complete AXI-Lite agent (seq item, driver, monitor, agent)
- `examples/axi_lite_scoreboard.sv` — dual-FIFO scoreboard with run_phase compare loop
