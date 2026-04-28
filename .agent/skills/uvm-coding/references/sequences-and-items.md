# Sequences and Sequence Items

> Full sequence item API, sequence body idioms, virtual sequences, and sequencer arbitration.

## Full `uvm_sequence_item` with `do_copy` / `do_compare`

```systemverilog
class axi_item extends uvm_sequence_item;
    `uvm_object_utils_begin(axi_item)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(we,   UVM_ALL_ON)
    `uvm_object_utils_end

    rand logic [31:0] addr;
    rand logic [31:0] data;
    rand logic        we;

    constraint c_align { addr[1:0] == 2'b00; }

    function new(string name = "axi_item");
        super.new(name);
    endfunction

    // do_copy: called by item.copy(src) — deep copy all fields
    function void do_copy(uvm_object rhs);
        axi_item rhs_;
        super.do_copy(rhs);
        if (!$cast(rhs_, rhs)) `uvm_fatal("TYPE", "do_copy type mismatch")
        addr = rhs_.addr;
        data = rhs_.data;
        we   = rhs_.we;
    endfunction

    // do_compare: called by item.compare(other) — field-by-field check
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

**Note:** `uvm_field_*` macros auto-implement `do_copy`/`do_compare`/`do_print`/`do_pack`
but have runtime overhead. Explicit implementations (shown above) are preferred in performance-
sensitive environments. Use one approach — not both.

---

## Sequence body(): three idioms

### Idiom 1: `uvm_do_with` macro (most common)
```systemverilog
task body();
    `uvm_do_with(req, { we == 1'b1; addr < 32'h200; })
endtask
```
Expands to: create item → start_item → randomize with constraint → finish_item.

### Idiom 2: Explicit `start_item` / `finish_item`
```systemverilog
task body();
    req = axi_item::type_id::create("req");
    start_item(req);                            // grants sequencer access; may block
    if (!req.randomize() with { we == 1'b1; })
        `uvm_fatal("RAND", "randomize failed")
    finish_item(req);                           // sends to driver; blocks until item_done
endtask
```
Use this when you need to set fields between `start_item` and `finish_item` that depend
on state not known at randomization time.

### Idiom 3: `do-while` for rejection sampling
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
Useful when a constraint is impractical to express in SV syntax but easy to check post-randomize.

---

## `p_sequencer`: accessing agent config from a sequence

`p_sequencer` gives a sequence typed access to its sequencer, which can hold agent-level config.

```systemverilog
// In the sequencer:
class axi_sequencer extends uvm_sequencer #(axi_item);
    `uvm_component_utils(axi_sequencer)
    axi_config cfg;   // set by agent in build_phase
    function new(string name, uvm_component parent); super.new(name, parent); endfunction
endclass

// In the sequence — declare p_sequencer type:
class axi_cfg_seq extends uvm_sequence #(axi_item);
    `uvm_object_utils(axi_cfg_seq)
    `uvm_declare_p_sequencer(axi_sequencer)   // casts m_sequencer to axi_sequencer

    task body();
        // p_sequencer.cfg is now accessible
        `uvm_do_with(req, { addr < p_sequencer.cfg.max_addr; })
    endtask
endclass
```

---

## Virtual sequences: coordinating multiple sub-sequencers

```systemverilog
class axi_virtual_seq extends uvm_sequence;
    `uvm_object_utils(axi_virtual_seq)

    // Handles to sub-sequencers — set by the test before start()
    axi_sequencer  axi_sqr;
    apb_sequencer  apb_sqr;

    task body();
        axi_write_seq  wr_seq;
        apb_config_seq cfg_seq;

        fork
            begin
                cfg_seq = apb_config_seq::type_id::create("cfg_seq");
                cfg_seq.start(apb_sqr);
            end
            begin
                wr_seq = axi_write_seq::type_id::create("wr_seq");
                wr_seq.start(axi_sqr);
            end
        join
    endtask
endclass
```

**Key rule:** a virtual sequence has no item type parameter (`uvm_sequence` not `uvm_sequence #(T)`)
and is started on a `null` sequencer or a dedicated virtual sequencer. Sub-sequencer handles
must be assigned before `start()`.

---

## Sequence priority and arbitration modes

The sequencer arbitrates between multiple sequences running concurrently.

| Mode | Behavior | When to use |
|---|---|---|
| `SEQ_ARB_FIFO` (default) | Round-robin in arrival order | Most cases |
| `SEQ_ARB_WEIGHTED` | Weighted random selection | Prioritized traffic |
| `SEQ_ARB_RANDOM` | Uniform random | Stress/random interleaving |
| `SEQ_ARB_STRICT_FIFO` | Strict priority by sequence priority field | Ordered protocol compliance |
| `SEQ_ARB_STRICT_RANDOM` | Strict priority, random within same level | Mixed traffic |

```systemverilog
// Set arbitration mode in env connect_phase or test body:
env.agent.sqr.set_arbitration(SEQ_ARB_WEIGHTED);

// Set sequence priority when starting:
high_prio_seq.start(sqr, .parent_sequence(null), .priority(200));
low_prio_seq.start(sqr,  .parent_sequence(null), .priority(100));
```
