# Sequences and Sequence Items

> Full sequence-item API (do_copy / do_compare / convert2string), three
> body idioms, late randomization, sequence polymorphism, sequence library,
> arbitration modes, pipelined drivers, and the slave-driver pattern.

## Sequence item — full API

```systemverilog
class axi_item extends uvm_sequence_item;
    `uvm_object_utils(axi_item)

    rand logic [31:0] addr;
    rand logic [31:0] data;
    rand logic        we;

    constraint c_align { addr[1:0] == 2'b00; }

    function new(string name = "axi_item");
        super.new(name);
    endfunction

    // do_copy — called by item.copy(src)
    function void do_copy(uvm_object rhs);
        axi_item rhs_;
        super.do_copy(rhs);
        if (!$cast(rhs_, rhs)) `uvm_fatal("TYPE", "do_copy type mismatch")
        addr = rhs_.addr;
        data = rhs_.data;
        we   = rhs_.we;
    endfunction

    // do_compare — called by item.compare(other)
    function bit do_compare(uvm_object rhs, uvm_comparer comparer);
        axi_item rhs_;
        if (!$cast(rhs_, rhs)) return 0;
        return super.do_compare(rhs, comparer)
            && (addr === rhs_.addr)
            && (data === rhs_.data)
            && (we   === rhs_.we);
    endfunction

    function string convert2string();
        return $sformatf("[axi_item] addr=0x%08h data=0x%08h %s",
                         addr, data, we ? "WR" : "RD");
    endfunction
endclass
```

### Field automation macros — when to use them

`` `uvm_field_*(name, flags) `` macros auto-implement do_copy /
do_compare / do_print / do_pack via reflection.

| Pro | Con |
|---|---|
| Less boilerplate | 5×–10× simulation overhead per call |
| Free `print()`, `pack()`, etc | Buggy when fields are arrays of objects |
| Standard | Hides what's actually compared |

> **Cookbook §3.3 guideline**: hand-write `do_copy` / `do_compare` /
> `do_print` / `do_pack` / `do_unpack` in performance-critical
> testbenches. Field-automation macros are fine for small classes that
> are rarely copied/compared.

Pick **one approach per class** — never mix field-automation and hand-
written methods.

## Sequence body — three idioms

### Idiom 1 — `uvm_do_with` (most common)

```systemverilog
task body();
    `uvm_do_with(req, { we == 1'b1; addr < 32'h200; })
endtask
```

Expands to: `create` → `start_item` → `randomize with` → `finish_item`.

### Idiom 2 — explicit start_item / finish_item

```systemverilog
task body();
    req = axi_item::type_id::create("req");
    start_item(req);
    if (!req.randomize() with { we == 1'b1; })
        `uvm_fatal("RAND", "randomize failed")
    finish_item(req);
endtask
```

Use when you need to set fields *between* start_item and finish_item
based on state unavailable at the `uvm_do_with` site.

### Idiom 3 — rejection sampling

```systemverilog
task body();
    req = axi_item::type_id::create("req");
    do begin
        void'(req.randomize());
    end while (req.addr inside {BLACKLIST});
    start_item(req);
    finish_item(req);
endtask
```

For constraints awkward in SV syntax (e.g., dynamic blacklist).

## Late randomization

A subtle pattern: randomize the item *just before* the driver consumes
it, using values available only at that moment.

```systemverilog
task body();
    req = axi_item::type_id::create("req");
    start_item(req);              // grants sequencer arbitration
    // ... now we have access to current driver state, p_sequencer ...
    if (!req.randomize() with {
        addr == p_sequencer.cfg.next_addr;
    }) `uvm_fatal("RAND", "late randomize failed")
    finish_item(req);             // sends to driver
endtask
```

Difference from idiom 1: `uvm_do_with` randomizes *before* start_item.
Late randomization randomizes *between* start_item and finish_item, so
state-dependent constraints can use values that are valid only at the
moment of arbitration.

> **Cookbook §4.2 guideline**: prefer late randomization for state-
> dependent constraints; use `uvm_do_with` for purely declarative
> constraints. Don't randomize in `pre_body()` — too early.

## p_sequencer — typed sequencer access

```systemverilog
class axi_sequencer extends uvm_sequencer #(axi_item);
    `uvm_component_utils(axi_sequencer)
    axi_config cfg;
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
endclass

class axi_cfg_seq extends uvm_sequence #(axi_item);
    `uvm_object_utils(axi_cfg_seq)
    `uvm_declare_p_sequencer(axi_sequencer)   // p_sequencer typed as axi_sequencer

    task body();
        `uvm_do_with(req, { addr < p_sequencer.cfg.max_addr; })
    endtask
endclass
```

Without the `` `uvm_declare_p_sequencer `` macro, `p_sequencer` exists
as `uvm_sequencer` base type — no agent-specific fields accessible.

## Sequence polymorphism

Tests can override which sequence type is created via the factory:

```systemverilog
// Base sequence
class axi_base_seq extends uvm_sequence #(axi_item);
    `uvm_object_utils(axi_base_seq)
    function new(string name = "axi_base_seq"); super.new(name); endfunction
    virtual task body();
        `uvm_do_with(req, { we == 1'b1; })
    endtask
endclass

// Variant
class axi_burst_seq extends axi_base_seq;
    `uvm_object_utils(axi_burst_seq)
    function new(string name = "axi_burst_seq"); super.new(name); endfunction
    virtual task body();
        repeat (8) `uvm_do_with(req, { we == 1'b1; })
    endtask
endclass

// In the test build_phase — swap one for another
function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    axi_base_seq::type_id::set_type_override(axi_burst_seq::get_type());
    // ... env construction
endfunction
```

Every place that creates an `axi_base_seq` via the factory gets an
`axi_burst_seq` instead. Useful for test variants that share scaffolding
but differ in stimulus.

## Sequence Library

`uvm_sequence_library #(T)` runs a randomly chosen sequence from a
registered set, useful for stress testing:

```systemverilog
class axi_seq_lib extends uvm_sequence_library #(axi_item);
    `uvm_object_utils(axi_seq_lib)
    `uvm_sequence_library_utils(axi_seq_lib)

    function new(string name = "axi_seq_lib");
        super.new(name);
        init_sequence_library();
    endfunction
endclass

// Register sequences once (e.g., in package init):
axi_write_seq::add_typewide_sequence(axi_seq_lib::get_type());
axi_read_seq::add_typewide_sequence(axi_seq_lib::get_type());
axi_burst_seq::add_typewide_sequence(axi_seq_lib::get_type());

// In a test or virtual sequence:
task body();
    axi_seq_lib lib = axi_seq_lib::type_id::create("lib");
    lib.selection_mode = UVM_SEQ_LIB_RANDC;     // each variant before repeat
    lib.min_random_count = 50;
    lib.max_random_count = 100;
    lib.start(sqr);
endtask
```

Selection modes:
- `UVM_SEQ_LIB_RAND` — uniform random
- `UVM_SEQ_LIB_RANDC` — cyclic random (each before repeats)
- `UVM_SEQ_LIB_ITEM` — pick each sequence in registration order

## Arbitration modes (sequencer)

When multiple sequences run concurrently on one sequencer:

| Mode | Behavior | Use |
|---|---|---|
| `SEQ_ARB_FIFO` (default) | Round-robin in arrival order | Default for most tests |
| `SEQ_ARB_WEIGHTED` | Weighted random | Prioritized traffic |
| `SEQ_ARB_RANDOM` | Uniform random | Stress / interleaving |
| `SEQ_ARB_STRICT_FIFO` | Strict priority, FIFO within level | Protocol compliance |
| `SEQ_ARB_STRICT_RANDOM` | Strict priority, random within level | Mixed-priority |

```systemverilog
env.agent.sqr.set_arbitration(SEQ_ARB_WEIGHTED);

high_prio_seq.start(sqr, .parent_sequence(null), .priority(200));
low_prio_seq.start(sqr,  .parent_sequence(null), .priority(100));
```

## Pipelined driver — `get`/`put` pattern

The standard `get_next_item` / `item_done` pattern is for **unpipelined**
protocols (one outstanding transaction). Pipelined protocols (AXI4,
AHB, PCIe) need multiple outstanding transactions.

### Pipelined pattern using `get` and `put`

```systemverilog
// Driver — get the item, fork the response handling
task run_phase(uvm_phase phase);
    forever begin
        my_item req;
        seq_item_port.get(req);              // non-blocking: pop one item
        fork
            automatic my_item req_local = req;
            begin
                drive_address(req_local);    // address phase
                wait_response(req_local);    // data phase later
                seq_item_port.put(req_local); // return result item
            end
        join_none
    end
endtask
```

### Sequence — start_item / finish_item / get_response

```systemverilog
task body();
    repeat (8) begin
        my_item req = my_item::type_id::create("req");
        start_item(req);
        assert(req.randomize());
        finish_item(req);
        // Don't block here on response — let pipeline fill
    end

    // Then collect responses
    repeat (8) begin
        my_item rsp;
        get_response(rsp);
        // ... compare ...
    end
endtask
```

> **Cookbook §10**: pipelined drivers use `get`/`put` instead of
> `get_next_item`/`item_done`. The sequence sends items without
> blocking on each; responses are collected separately.

## Slave driver — bidirectional response

A slave responds to bus-level requests with data. Pattern:

```systemverilog
// Slave sequence: "tell me what to do"
class slave_seq extends uvm_sequence #(slave_item);
    task body();
        slave_item req, rsp;
        forever begin
            req = slave_item::type_id::create("req");
            start_item(req);
            finish_item(req);            // driver fills req with bus details
            // Compute response
            rsp = slave_item::type_id::create("rsp");
            rsp.data = lookup(req.addr);
            start_item(rsp);
            finish_item(rsp);
        end
    endtask
endclass

// Slave driver:
task run_phase(uvm_phase phase);
    slave_item req, rsp;
    forever begin
        // Step 1: wait for bus request, get item from seq for "what to do"
        @(posedge vif.req);
        seq_item_port.get_next_item(req);
        req.addr = vif.addr;
        req.we   = vif.we;
        seq_item_port.item_done();
        // Step 2: get response item from seq
        seq_item_port.get_next_item(rsp);
        vif.rdata <= rsp.data;
        @(posedge vif.clk);
        seq_item_port.item_done();
    end
endtask
```

Two get_next_item calls per bus transaction: one to get request
context, one to get response data.

## Interrupt-driven stimulus

When the test must inject stimulus on a hardware event (interrupt):

```systemverilog
class isr_seq extends uvm_sequence #(reg_item);
    task body();
        forever begin
            @(posedge p_sequencer.isr_event);
            // Read interrupt status, clear, etc.
            `uvm_do_with(req, {
                addr == ISR_STATUS_ADDR;
                we   == 1'b0;
            })
        end
    endtask
endclass
```

The sequencer exposes `isr_event` (e.g., a `uvm_event` signaled by the
monitor when an interrupt is detected). The ISR sequence runs in
parallel with the main sequence. Arbitration determines the order
when both want to send items.

Use **strict priority** so ISR pre-empts normal traffic:

```systemverilog
sqr.set_arbitration(SEQ_ARB_STRICT_FIFO);
main_seq.start(sqr, .priority(100));
isr_seq.start(sqr,  .priority(200));     // higher priority — wins
```

## Common pitfalls

- **`randomize()` return ignored.** Use `assert(... .randomize() with {...})`.
- **No `convert2string()` in the item.** UVM message logs become useless.
- **`uvm_do_with` with a constraint referencing a non-class variable.**
  The macro doesn't capture scope properly; spell out via Idiom 2.
- **`p_sequencer` access without the macro.** Type-erased; agent
  fields not accessible.
- **Pipelined sequence using `finish_item` then expecting blocking
  response.** `finish_item` returns when driver got the item, not when
  the bus completes. Use `get_response()`.
- **Slave driver with one `get_next_item` per bus event.** Returns the
  same item — `item_done()` then `get_next_item()` again for the
  response.
- **Sequence library with `init_sequence_library()` forgotten.** All
  sequences registered to the library type-wide will be invisible.
- **Forgetting `uvm_sequence_library_utils(T)`.** Companion macro to
  `uvm_object_utils` for sequence libraries.

## Citations

- **Mentor Graphics UVM Cookbook**, *Sequences* / *Driver Use Models*
  / *Sequence Library* chapters — body idioms, late randomization,
  pipelined / slave patterns, sequence library API.
- **Accellera UVM 1.2 §12** — sequence/sequencer/driver API.

## See also

- `component-architecture.md` — sequencer / driver wiring.
- `virtual-sequences-and-layering.md` — multi-agent and layered
  sequence patterns.
- `analysis-ports-and-scoreboards.md` — get_response and analysis
  feedback to sequence.
- `objections-deep-dive.md` — sequences and objection propagation.
