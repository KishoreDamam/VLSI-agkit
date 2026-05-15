# UVM Component Architecture

> Factory registration, factory overrides catalog, virtual interface
> pattern (config_db + package-based), config_db precedence rules,
> active/passive agent, build/connect process detail, and dual-top
> testbench structure.

## UVM component hierarchy

```
uvm_top (implicit root)
  └─ uvm_test_top (uvm_test, selected via +UVM_TESTNAME)
       └─ env (uvm_env)
            ├─ block_env (block-level sub-env)
            │    └─ agent (uvm_agent)
            │         ├─ sequencer (uvm_sequencer)
            │         ├─ driver    (uvm_driver)     ← active only
            │         └─ monitor   (uvm_monitor)
            ├─ scoreboard (uvm_scoreboard)
            ├─ predictor  (uvm_reg_predictor or custom)
            └─ coverage   (uvm_subscriber)
```

The env composes other envs (block-level → integration-level → SoC).
At the bottom of every protocol leaf is an **agent**.

## The Agent

An agent encapsulates everything needed to drive and monitor *one*
protocol:

```systemverilog
class apb_agent extends uvm_agent;
    `uvm_component_utils(apb_agent)

    apb_agent_config cfg;          // injected by env
    apb_driver       drv;
    apb_sequencer    sqr;
    apb_monitor      mon;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(apb_agent_config)::get(this, "", "cfg", cfg))
            `uvm_fatal("CFG", "no agent config")
        mon = apb_monitor::type_id::create("mon", this);
        if (cfg.is_active == UVM_ACTIVE) begin
            drv = apb_driver::type_id::create("drv", this);
            sqr = apb_sequencer::type_id::create("sqr", this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if (cfg.is_active == UVM_ACTIVE)
            drv.seq_item_port.connect(sqr.seq_item_export);
    endfunction
endclass
```

Active vs passive: the monitor always exists; the driver and sequencer
only exist when `is_active == UVM_ACTIVE`. Lets the same agent be
reused both to drive a master interface and to passively monitor a
slave interface.

## The Env (block vs integration)

### Block-level env

Contains one or two agents and their direct scoreboard. Used as a
**standalone testbench** at the IP level.

```systemverilog
class spi_env extends uvm_env;
    `uvm_component_utils(spi_env)
    spi_agent        agent;
    spi_scoreboard   sb;
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        agent = spi_agent::type_id::create("agent", this);
        sb    = spi_scoreboard::type_id::create("sb",    this);
    endfunction
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        agent.mon.ap.connect(sb.actual_fifo.analysis_export);
    endfunction
endclass
```

### Integration-level env

Composes multiple block-level envs plus integration scoreboard /
virtual sequencer.

```systemverilog
class chip_env extends uvm_env;
    `uvm_component_utils(chip_env)

    apb_env         apb_block;
    spi_env         spi_block;
    chip_v_sqr      v_sqr;
    chip_scoreboard sb;

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        apb_block = apb_env::type_id::create("apb_block", this);
        spi_block = spi_env::type_id::create("spi_block", this);
        v_sqr     = chip_v_sqr::type_id::create("v_sqr",   this);
        sb        = chip_scoreboard::type_id::create("sb", this);
    endfunction

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        v_sqr.apb_sqr = apb_block.agent.sqr;
        v_sqr.spi_sqr = spi_block.agent.sqr;
        apb_block.agent.mon.ap.connect(sb.apb_actual.analysis_export);
        spi_block.agent.mon.ap.connect(sb.spi_actual.analysis_export);
    endfunction
endclass
```

Block envs are reusable across projects; integration envs are
project-specific.

## Factory registration

| Macro | Applies to | Constructor |
|---|---|---|
| `` `uvm_component_utils(T) `` | `uvm_component` subclasses | `new(name, parent)` |
| `` `uvm_object_utils(T) `` | `uvm_object` subclasses (items, sequences, configs) | `new(name = "T")` |
| `` `uvm_component_param_utils(T) `` | Parameterized component | Same as component |
| `` `uvm_object_param_utils(T) `` | Parameterized object | Same as object |

For parameterized classes:

```systemverilog
class my_param_comp #(int W = 32) extends uvm_component;
    typedef my_param_comp #(W) this_t;
    `uvm_component_param_utils(this_t)
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
endclass
```

## Factory overrides — full catalog

The factory lets the test substitute one type for another *without
changing the env code*. Four mechanisms:

### 1. Component type override

Every place that creates `apb_driver` instead creates `apb_debug_driver`:

```systemverilog
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    apb_driver::type_id::set_type_override(apb_debug_driver::get_type());
    env = chip_env::type_id::create("env", this);
endfunction
```

### 2. Component instance override

Only one specific instance gets replaced:

```systemverilog
apb_driver::type_id::set_inst_override(
    apb_debug_driver::get_type(),
    "uvm_test_top.env.apb_block.agent.drv"
);
```

### 3. Object type override

Same as component type but for sequences / items / configs:

```systemverilog
apb_seq_item::type_id::set_type_override(apb_corrupt_item::get_type());
```

### 4. Object instance override

Per-context object substitution. Less common.

```systemverilog
apb_seq_item::type_id::set_inst_override(
    apb_corrupt_item::get_type(),
    "uvm_test_top.env.apb_block.agent.sqr.req"
);
```

### Calling overrides

```systemverilog
// Register the type override before env construction:
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    apb_driver::type_id::set_type_override(apb_debug_driver::get_type());
    env = chip_env::type_id::create("env", this);
endfunction
```

Order matters: override must happen **before** the targeted `create()`.

## `uvm_config_db` — set / get pattern

### Set (top-level)

```systemverilog
// In top-level testbench module
initial begin
    uvm_config_db#(virtual apb_if)::set(
        null,                                  // context: null = uvm_top
        "uvm_test_top.env.apb_block.agent.*",  // path glob
        "vif",                                 // field name
        u_apb_if                                // value
    );
    run_test();
end
```

### Get (in component)

```systemverilog
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual apb_if)::get(this, "", "vif", vif))
        `uvm_fatal("NOVIF", {"VIF missing at ", get_full_name()})
endfunction
```

### Precedence rules

When multiple `set()` calls target the same field at overlapping
paths, the higher-precedence one wins. Rules:

1. **More-specific path wins.** `uvm_test_top.env.apb_block.agent.drv`
   beats `uvm_test_top.*`.
2. **Earlier set() wins on ties.** First-set-wins by default.
3. **Latest set() wins** if `set_default_precedence` is changed.

Debug via `+UVM_CONFIG_DB_TRACE`.

## Virtual interface — package pattern

A common modern pattern: declare a typedef in a package, set it once,
agents grab it via config_db.

### Step 1 — declare virtual interface type in a package

```systemverilog
// File: chip_params_pkg.sv
package chip_params_pkg;
    // (Note: virtual interfaces can't go in package — interfaces are not
    // class types — but the type alias for handles can.)
    parameter int APB_ADDR_WIDTH = 32;
    parameter int APB_DATA_WIDTH = 32;
endpackage
```

```systemverilog
// File: apb_if.sv (NOT in package — it's an interface)
interface apb_if (input pclk);
    logic        psel, penable, pwrite, pready, pslverr;
    logic [31:0] paddr, pwdata, prdata;

    modport mp (
        input  pclk,
        output psel, penable, pwrite, paddr, pwdata,
        input  pready, pslverr, prdata
    );
endinterface
```

### Step 2 — instantiate in top module and set via config_db

```systemverilog
// File: hdl_top.sv
module hdl_top;
    logic pclk;
    apb_if u_apb_if (.pclk);
    dut u_dut (...);

    initial begin
        uvm_config_db#(virtual apb_if)::set(
            null, "uvm_test_top.*", "apb_vif", u_apb_if);
        run_test();
    end
endmodule
```

### Step 3 — agent fetches it

```systemverilog
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual apb_if)::get(this, "", "apb_vif", vif))
        `uvm_fatal("NOVIF", "apb_vif missing")
endfunction
```

Why this pattern: the interface lives at the HDL level (must), but the
testbench at any level can ask for it without hierarchical references.
Tests can override the interface (for stubbing) via type override on a
wrapper class.

## Multiple interface instances

For two instances of the same agent (e.g., dual APB ports), set them
separately with distinct field names:

```systemverilog
// hdl_top:
apb_if u_apb_a (.pclk);
apb_if u_apb_b (.pclk);

uvm_config_db#(virtual apb_if)::set(
    null, "uvm_test_top.env.apb_a_block.agent.*", "vif", u_apb_a);
uvm_config_db#(virtual apb_if)::set(
    null, "uvm_test_top.env.apb_b_block.agent.*", "vif", u_apb_b);
```

Each agent's path glob targets the right interface. Field name "vif"
is unchanged.

## Phase ordering — build vs connect

### `build_phase` — top-down

Parent build runs first. Use it to create children with `type_id::create`.

```systemverilog
function void build_phase(uvm_phase phase);
    super.build_phase(phase);          // always call super first
    monitor = my_monitor::type_id::create("monitor", this);
    if (get_is_active() == UVM_ACTIVE) begin
        driver    = my_driver::type_id::create("driver", this);
        sequencer = my_sequencer::type_id::create("sequencer", this);
    end
endfunction
```

### `connect_phase` — bottom-up

Children connect first. Never create components here.

```systemverilog
function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (get_is_active() == UVM_ACTIVE)
        driver.seq_item_port.connect(sequencer.seq_item_export);
    monitor.ap.connect(scoreboard.actual_fifo.analysis_export);
endfunction
```

## Dual-top testbench

Two top-level modules — `hdl_top` (DUT side) and `tb_top` (UVM side):

```systemverilog
// hdl_top.sv
module hdl_top;
    logic clk, rst_n;
    initial begin clk = 0; forever #5 clk = ~clk; end
    initial begin rst_n = 0; #50 rst_n = 1; end

    apb_if u_apb_if (.pclk(clk));
    dut    u_dut (.clk(clk), .rst_n(rst_n), /* apb pins */);

    initial uvm_config_db#(virtual apb_if)::set(
        null, "uvm_test_top.*", "apb_vif", u_apb_if);
endmodule

// tb_top.sv
module tb_top;
    initial run_test();
endmodule
```

Run both: `vsim hdl_top tb_top +UVM_TESTNAME=my_test`.

Benefit: cleaner separation, easier to swap testbench independently
of the DUT, and required for two-kingdoms emulation (see
`two-kingdoms-emulation.md`).

## Phase objection — required for time-consuming phases

```systemverilog
task run_phase(uvm_phase phase);
    phase.raise_objection(this, "starting main_seq");
    main_seq = my_seq::type_id::create("main_seq");
    main_seq.start(env.agent.sqr);
    #(10 * PERIOD);
    phase.drop_objection(this, "main_seq done");
endtask
```

See `objections-deep-dive.md` for the full mechanics.

## Common pitfalls

- **`super.<phase>(phase)` missing.** Always call it first.
- **Component created in `connect_phase`.** Phase is for wiring only;
  all components must exist by then.
- **`set()` called *after* the child's build_phase.** Top-down ordering
  means the parent's build_phase runs before the child's. The `set()`
  must happen in the parent's build before the parent calls
  `create()` on the child.
- **Wildcards too broad in config_db path.** `"*"` matches everywhere
  and can cause cross-contamination. Use specific globs.
- **Factory override called *after* `create()`.** Override must
  precede the create call.
- **Multiple sets to the same field without precedence understood.**
  First-set-wins by default; `+UVM_CONFIG_DB_TRACE` shows what's
  active.
- **`new()` instead of `type_id::create()` for components.** Bypasses
  the factory.
- **Hierarchical reference to DUT signals in the testbench.** Breaks
  emulation; breaks portability. Use config_db with virtual interface
  handle.

## Citations

- **Mentor Graphics UVM Cookbook**, *UVM Testbench Hierarchy* /
  *Factory* / *Configuration Objects* / *Virtual Interfaces* /
  *DualTop* chapters.
- **Accellera UVM 1.2 §5–§9** — factory, config_db, phase ordering.

## See also

- `phasing-deep-dive.md` — every phase explained.
- `objections-deep-dive.md` — raise/drop mechanics.
- `uvm-package-structure.md` — package layout for the env / agents
  shown here.
- `two-kingdoms-emulation.md` — dual-top pattern for emulation.
- `messaging-and-debug.md` — `+UVM_CONFIG_DB_TRACE`, `+UVM_FACTORY_TRACE`.
