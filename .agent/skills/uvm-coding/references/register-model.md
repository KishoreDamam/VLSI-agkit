# UVM Register Model (RAL)

> Register abstraction layer: building the model, integration via
> adapter and predictor, access methods (read/write/peek/poke/mirror/
> update), built-in test sequences, backdoor HDL paths, quirky-register
> callbacks, register-based scoreboard, and RAL-driven coverage.

## RAL architecture

```
Test / Sequence
      │
      ▼   .write() / .read() / .mirror() / .update()
   uvm_reg_block      ← models the DUT's CSR map
      │
      ▼
   uvm_reg_map        ← address layout
      │
      ▼
   uvm_reg_adapter    ← translate reg op ↔ bus item
      │
      ▼
   uvm_reg_predictor  ← passive: update mirror from observed traffic
      │
      ▼
   Bus Agent          ← drives actual bus protocol
      │
      ▼   pins
    DUT
```

## Building the model

### Field, register, block

```systemverilog
// Register definition
class ctrl_reg extends uvm_reg;
    `uvm_object_utils(ctrl_reg)

    rand uvm_reg_field enable;     // bit 0
    rand uvm_reg_field mode;       // bits 2:1
    rand uvm_reg_field rsvd;       // bits 31:3

    function new(string name = "ctrl_reg");
        super.new(name, 32, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        enable = uvm_reg_field::type_id::create("enable");
        mode   = uvm_reg_field::type_id::create("mode");
        rsvd   = uvm_reg_field::type_id::create("rsvd");

        // configure(parent, n_bits, lsb_pos, access, volatile,
        //           reset, has_reset, is_rand, individually_accessible)
        enable.configure(this, 1,  0, "RW", 0, 1'b0,         1, 1, 0);
        mode.configure  (this, 2,  1, "RW", 0, 2'b00,        1, 1, 0);
        rsvd.configure  (this, 29, 3, "RO", 0, 29'h0,        1, 0, 0);
    endfunction
endclass

// Register block (CSR map)
class chip_reg_block extends uvm_reg_block;
    `uvm_object_utils(chip_reg_block)

    rand ctrl_reg ctrl;
    rand stat_reg stat;
    uvm_reg_map   default_map;

    function new(string name = "chip_reg_block");
        super.new(name, UVM_NO_COVERAGE);
    endfunction

    virtual function void build();
        default_map = create_map("default_map", 32'h0, 4, UVM_LITTLE_ENDIAN);

        ctrl = ctrl_reg::type_id::create("ctrl");
        ctrl.build();
        ctrl.configure(this);
        default_map.add_reg(ctrl, 32'h00, "RW");

        stat = stat_reg::type_id::create("stat");
        stat.build();
        stat.configure(this);
        default_map.add_reg(stat, 32'h04, "RO");

        lock_model();                  // MUST be last
    endfunction
endclass
```

Field access types: `RW`, `RO`, `WO`, `W1C` (write-1-to-clear), `W1S`
(write-1-to-set), `RC` (read-to-clear), `RS` (read-to-set), `WRC`,
`WRS`, `WSRC`, `WCRS`, `W1` (write once), `WO1`, `NOACCESS`. Use the
ones that match the DUT spec.

## Adapter — bus translation

The adapter converts between generic `uvm_reg_bus_op` and the bus
agent's sequence item:

```systemverilog
class apb_reg_adapter extends uvm_reg_adapter;
    `uvm_object_utils(apb_reg_adapter)

    function new(string name = "apb_reg_adapter");
        super.new(name);
        supports_byte_enable = 0;
        provides_responses   = 0;
    endfunction

    // RAL wants to do a write/read → produce a bus item
    virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
        apb_seq_item item = apb_seq_item::type_id::create("item");
        item.addr = rw.addr;
        item.data = rw.data;
        item.we   = (rw.kind == UVM_WRITE) ? 1'b1 : 1'b0;
        return item;
    endfunction

    // Monitor observed a bus item → tell RAL what register operation happened
    virtual function void bus2reg(uvm_sequence_item bus_item,
                                   ref uvm_reg_bus_op rw);
        apb_seq_item item;
        if (!$cast(item, bus_item))
            `uvm_fatal("CAST", "bus2reg: item not apb_seq_item")
        rw.kind   = item.we ? UVM_WRITE : UVM_READ;
        rw.addr   = item.addr;
        rw.data   = item.data;
        rw.status = UVM_IS_OK;
    endfunction
endclass
```

> **Cookbook §13**: both `reg2bus` and `bus2reg` are required.
> `bus2reg` is what lets the predictor work. Skipping it means passive
> mirror updates fail silently.

## Predictor — passive mirror updates

```systemverilog
// In env build_phase
uvm_reg_predictor #(apb_seq_item) predictor;
predictor = uvm_reg_predictor#(apb_seq_item)::type_id::create("predictor", this);

// In env connect_phase
predictor.map     = reg_block.default_map;
predictor.adapter = adapter;
monitor.ap.connect(predictor.bus_in);
```

For each observed transaction the predictor calls `adapter.bus2reg()`,
finds the matching register via the map, and updates the register's
mirrored value. Two modes:

| Mode | Set by | Behavior |
|---|---|---|
| **Auto prediction** | `reg_block.default_map.set_auto_predict(1)` | RAL updates mirror immediately after every `.write()` / `.read()` |
| **Passive prediction** | Default; predictor wired to monitor | Mirror updated only when monitor sees the bus traffic |

Use passive for full coverage of mirror correctness. Use auto when the
testbench cannot observe the bus path (e.g., backdoor-only tests).

## Integration

```systemverilog
// In test build_phase
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = chip_env::type_id::create("env", this);
endfunction

// In env build_phase
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (reg_block == null) begin
        reg_block = chip_reg_block::type_id::create("reg_block");
        reg_block.build();
        reg_block.lock_model();
        reg_block.reset();
    end
    agent     = apb_agent::type_id::create("agent", this);
    adapter   = apb_reg_adapter::type_id::create("adapter");
    predictor = uvm_reg_predictor#(apb_seq_item)::type_id::create("predictor", this);
endfunction

// In env connect_phase
function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    reg_block.default_map.set_sequencer(agent.sqr, adapter);
    predictor.map     = reg_block.default_map;
    predictor.adapter = adapter;
    agent.monitor.ap.connect(predictor.bus_in);
endfunction
```

## Access methods

| Method | What it does |
|---|---|
| `reg.write(status, data, .map(m))` | Bus write; updates mirror |
| `reg.read(status, data, .map(m))` | Bus read; updates mirror |
| `reg.peek(status, data)` | Backdoor read; no bus traffic |
| `reg.poke(status, data)` | Backdoor write; no bus traffic |
| `reg.set(data)` | Set desired value in mirror only (no bus) |
| `reg.get()` | Get desired value from mirror |
| `reg.update(status, .map(m))` | If mirror dirty (different from desired), write to DUT |
| `reg.mirror(status, .check(c), .map(m))` | Bus read; optionally compare against mirror |

### `set + update` vs `write`

```systemverilog
// Pattern A — write each field separately
regs.ctrl.write(status, 32'h0000_0005);

// Pattern B — set fields in mirror, then update bus once
regs.ctrl.enable.set(1);
regs.ctrl.mode.set(2'b10);
regs.ctrl.update(status);          // one bus write with combined value
```

Pattern B is more readable when setting many fields of one register;
RAL combines them into a single bus write.

### `mirror` for end-of-test checks

```systemverilog
// Compare every register's DUT value against expected mirror
uvm_reg regs_arr[$];
reg_block.get_registers(regs_arr);
foreach (regs_arr[i]) begin
    regs_arr[i].mirror(status, UVM_CHECK);
end
```

`UVM_CHECK` makes the mirror call compare automatically.

## Built-in test sequences

| Sequence | What it does |
|---|---|
| `uvm_reg_hw_reset_seq` | Read every register and compare to its reset value |
| `uvm_reg_bit_bash_seq` | Walking-1s and walking-0s through all RW fields |
| `uvm_reg_access_seq` | Write each RW register and read back |
| `uvm_reg_shared_access_seq` | For registers shared between maps |
| `uvm_reg_single_*` variants | Per-register versions |
| `uvm_mem_walk_seq` | Memory: every location |
| `uvm_mem_access_seq` | Memory: write/read sample |

Run them like any sequence:

```systemverilog
task main_phase(uvm_phase phase);
    uvm_reg_hw_reset_seq reset_seq;
    phase.raise_objection(this);
    reset_seq = uvm_reg_hw_reset_seq::type_id::create("reset_seq");
    reset_seq.model = env.reg_block;
    reset_seq.start(env.agent.sqr);
    phase.drop_objection(this);
endtask
```

### Disabling built-in sequences per register

For registers that shouldn't be touched by the bit-bash (e.g., status
registers with side effects):

```systemverilog
// In reg_block.build():
uvm_resource_db #(bit)::set({"REG::", regs.intr_clear.get_full_name()},
                              "NO_REG_BIT_BASH_TEST", 1);
```

Each built-in sequence respects a documented attribute key. See cookbook
§13.5 for the full list.

## Backdoor access — HDL path

Backdoor reads/writes the DUT register signal directly, bypassing the
bus. Useful for:

- Fast init of large memory arrays.
- Probing internal state for checking.
- Tests where bus traffic isn't yet possible (early bring-up).

```systemverilog
// In reg_block.build() — declare HDL paths
ctrl.add_hdl_path_slice("dut.csr_block.ctrl_reg.enable_q", 0, 1);
ctrl.add_hdl_path_slice("dut.csr_block.ctrl_reg.mode_q",   1, 2);

// Backdoor read/write
regs.ctrl.peek(status, data);
regs.ctrl.poke(status, 32'hA5);
```

| Front-door | Backdoor |
|---|---|
| Tests RTL bus interface | Bypasses bus |
| Real silicon-like | Internal-signal access |
| Slow (full protocol) | Instant (force/release) |
| Use for default | Use for init / unobservable state |

Trade-off: **backdoor is invisible to RTL bus monitors and assertions**.
Use front-door for the actual test stimulus; backdoor only for setup
and end-of-test checks.

## Quirky registers — callbacks

Some registers don't behave like the standard `uvm_reg`:

- **ID register**: reads return a constant; writes ignored.
- **Free-running counter**: changes between reads.
- **Lock register**: read-only after first write.
- **Self-clearing**: written value disappears after one cycle.

Use callbacks to model special behavior:

```systemverilog
class id_reg_cbs extends uvm_reg_cbs;
    `uvm_object_utils(id_reg_cbs)

    function new(string name = "id_reg_cbs");
        super.new(name);
    endfunction

    // After read — override the value with the expected constant
    virtual task post_read(uvm_reg_item rw);
        rw.value[0] = 32'hDEAD_BEEF;
    endtask
endclass

// In reg_block.build():
id_reg_cbs cbs = id_reg_cbs::type_id::create("cbs");
uvm_reg_cb::add(regs.id_reg, cbs);
```

Callback hooks: `pre_write`, `post_write`, `pre_read`, `post_read`,
`encode`, `decode`. Most quirky registers can be modeled with one of
these.

## Register-based scoreboard

A scoreboard that uses RAL to check DUT behavior:

```systemverilog
class reg_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(reg_scoreboard)

    chip_reg_block reg_block;     // env injects this
    uvm_analysis_imp #(stat_event_item, reg_scoreboard) imp;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        imp = new("imp", this);
        if (!uvm_config_db#(chip_reg_block)::get(this, "", "reg_block", reg_block))
            `uvm_fatal("REGS", "no reg_block")
    endfunction

    // Compare DUT-observed event to expected register state
    function void write(stat_event_item item);
        uvm_reg_data_t expected = reg_block.stat.get();
        if (item.value !== expected)
            `uvm_error("REG_SB", $sformatf(
                "stat reg event 0x%0h doesn't match mirror 0x%0h",
                item.value, expected))
    endfunction
endclass
```

## Register-based functional coverage

The reg model can drive coverage automatically when built with
`UVM_CVR_FIELD_VALS` or `UVM_CVR_REG_BITS`:

```systemverilog
// In reg_block.build():
ctrl.include_coverage("ctrl", UVM_CVR_FIELD_VALS);
build_coverage(UVM_CVR_FIELD_VALS);   // enable in block
```

Each access (front-door or via mirror) triggers covergroup sampling on
the register's value. To control sampling explicitly:

```systemverilog
// Sample on a specific event
function void write(reg_event_item item);
    reg_block.ctrl.sample_values();
endfunction
```

## Common pitfalls

- **`lock_model()` forgotten** — registers added after lock cause runtime
  errors.
- **`adapter` and `predictor` not connected in `connect_phase`** —
  passive mirror updates fail silently; tests pass on `auto_predict`
  only.
- **Backdoor path uses wrong HDL hierarchy** — `add_hdl_path` strings
  go stale on RTL refactors; check against the synthesized hierarchy.
- **`peek`/`poke` instead of `write`/`read` for normal stimulus** —
  bypasses bus monitors; coverage misses; protocol bugs hide.
- **`set` + `write` confusion** — `set` only updates mirror; `update`
  pushes mirror to DUT; `write` pushes value to DUT and updates mirror.
- **`uvm_reg_bit_bash_seq` on registers with side effects** — DUT may
  hang or corrupt state. Use the `NO_REG_BIT_BASH_TEST` attribute.
- **Custom callbacks not added before first access** — order matters;
  add callbacks in `build_phase` before any sequence runs.
- **Multiple maps without map argument** — `.write(status, data)` uses
  the default map; specify `.map(specific_map)` for non-default.

## Citations

- **Mentor Graphics UVM Cookbook**, *Register Layer* /
  *Register Built-In Sequences* / *Backdoor Access* / *Quirky Registers*
  / *Register Coverage* / *Register Scoreboard* chapters.
- **Accellera UVM 1.2 §17–18** — RAL classes and API.

## See also

- `analysis-ports-and-scoreboards.md` — predictor connection from
  monitor.
- `sequences-and-items.md` — built-in sequences are normal sequences.
- `component-architecture.md` — env wiring of adapter, predictor.
- `messaging-and-debug.md` — `+UVM_RESOURCE_DB_TRACE` to debug
  attribute-based config.
