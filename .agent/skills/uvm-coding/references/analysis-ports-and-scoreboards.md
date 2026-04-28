# Analysis Ports and Scoreboards

> TLM analysis topology, FIFO adapters, built-in comparators, and coverage collectors.

## Port vs Export vs Imp — which side?

| Class | Who creates it | Direction | Connected to |
|---|---|---|---|
| `uvm_analysis_port #(T)` | Producer (monitor) | Output — calls `write()` | Analysis export or imp |
| `uvm_analysis_export #(T)` | Intermediary (FIFO, env pass-through) | Input | Passed through to an imp |
| `uvm_analysis_imp #(T, C)` | Consumer (scoreboard) | Input — implements `write()` | Source port |

**Mnemonic:** ports produce, exports/imps consume. Connect: `port.connect(export_or_imp)`.

```
monitor.ap (uvm_analysis_port)
    |
    +--> scoreboard.actual_fifo.analysis_export  (via uvm_tlm_analysis_fifo)
    +--> coverage.analysis_export                (uvm_subscriber wraps this)
```

---

## `uvm_tlm_analysis_fifo` — standard adapter between monitor and scoreboard

The FIFO exposes an `analysis_export` (input side) and `get()` (output side).
It is the standard way to decouple the monitor's `write()` rate from the scoreboard's `get()` rate.

```systemverilog
// In scoreboard build_phase:
uvm_tlm_analysis_fifo #(my_item) act_fifo;
act_fifo = new("act_fifo", this);   // FIFO uses new(), not type_id::create()

// In env connect_phase:
monitor.ap.connect(sb.act_fifo.analysis_export);

// In scoreboard run_phase:
my_item item;
act_fifo.get(item);   // blocking get — waits until item is in FIFO
```

**Why not a plain `uvm_analysis_imp`?** The `write()` function on an imp is zero-time — it
cannot block. If the scoreboard needs blocking operations (file writes, model queries),
the FIFO is essential.

---

## Dual-FIFO scoreboard pattern

```systemverilog
class my_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(my_scoreboard)

    uvm_tlm_analysis_fifo #(my_item) exp_fifo;  // reference model -> expected
    uvm_tlm_analysis_fifo #(my_item) act_fifo;  // monitor -> actual

    int unsigned pass_count, fail_count;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        exp_fifo = new("exp_fifo", this);
        act_fifo = new("act_fifo", this);
    endfunction

    task run_phase(uvm_phase phase);
        my_item exp_item, act_item;
        forever begin
            exp_fifo.get(exp_item);
            act_fifo.get(act_item);
            if (!act_item.do_compare(exp_item, null)) begin
                `uvm_error("SB_MISMATCH", $sformatf(
                    "EXP: %s  ACT: %s",
                    exp_item.convert2string(), act_item.convert2string()))
                fail_count++;
            end else begin
                `uvm_info("SB_PASS", act_item.convert2string(), UVM_HIGH)
                pass_count++;
            end
        end
    endtask

    function void check_phase(uvm_phase phase);
        if (exp_fifo.size() != 0)
            `uvm_error("SB_LEFTOVER", $sformatf(
                "%0d expected items never matched", exp_fifo.size()))
        `uvm_info("SB_SUMMARY", $sformatf(
            "Pass: %0d  Fail: %0d", pass_count, fail_count), UVM_NONE)
    endfunction
endclass
```

---

## `uvm_in_order_comparator` — built-in dual-FIFO comparator

`uvm_in_order_comparator #(T)` pairs expected and actual items in order and calls `T::do_compare()`.

```systemverilog
// In env:
uvm_in_order_comparator #(my_item) cmp;

// build_phase:
cmp = new("cmp", this);

// connect_phase:
ref_model.ap.connect(cmp.before_export);  // expected stream
monitor.ap.connect(cmp.after_export);     // actual stream
```

Limitations: strict in-order matching only; no custom logic without subclassing.
Use the dual-FIFO pattern for out-of-order or complex matching.

---

## `uvm_subscriber` — shorthand for monitor-side consumers

`uvm_subscriber #(T)` extends `uvm_component` and provides an `analysis_export` automatically.
Subclass it and implement `write(T t)`.

```systemverilog
class axi_coverage extends uvm_subscriber #(axi_item);
    `uvm_component_utils(axi_coverage)

    covergroup axi_cg;
        cp_addr:  coverpoint trans.addr[15:2];
        cp_we:    coverpoint trans.we;
        cx:       cross cp_addr, cp_we;
    endgroup

    axi_item trans;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        axi_cg = new();
    endfunction

    function void write(axi_item t);
        trans = t;
        axi_cg.sample();
    endfunction
endclass
```

Connect in env `connect_phase`:
```systemverilog
monitor.ap.connect(coverage.analysis_export);
```

---

## Multiple analysis imp ports on one scoreboard

If a scoreboard receives from multiple monitors, use `uvm_analysis_imp_decl`:

```systemverilog
`uvm_analysis_imp_decl(_expected)
`uvm_analysis_imp_decl(_actual)

class dual_sb extends uvm_scoreboard;
    `uvm_component_utils(dual_sb)
    uvm_analysis_imp_expected #(my_item, dual_sb) exp_imp;
    uvm_analysis_imp_actual   #(my_item, dual_sb) act_imp;

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        exp_imp = new("exp_imp", this);
        act_imp = new("act_imp", this);
    endfunction

    function void write_expected(my_item item); /* handle expected */ endfunction
    function void write_actual  (my_item item); /* handle actual   */ endfunction
endclass
```

The macro suffix (`_expected`, `_actual`) becomes the suffix on the `write_*` method name.
