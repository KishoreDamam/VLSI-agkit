# Analysis Ports, Monitors, Scoreboards & Predictors

> TLM analysis topology, monitor anatomy, predictor (proxy DUT) pattern,
> dual-FIFO scoreboard, built-in comparators, subscribers for coverage,
> and the post-run check/extract/report phases.

## The analysis path

```
   DUT ──→ monitor.ap ──┬──→ scoreboard.actual_fifo  ──┐
                        │                              │  compare
                        └──→ coverage.analysis_export   │
                                                       │
   DUT-ref-model ──→ predictor.ap ──→ scoreboard.expected_fifo
```

- **Monitor** observes the DUT and produces transaction objects.
- **Predictor** runs a reference model and produces expected transactions.
- **Scoreboard** matches expected against actual.
- **Coverage** subscribes to monitor output for functional coverage.

## Port / Export / Imp — which side?

| Class | Created by | Direction | Connects to |
|---|---|---|---|
| `uvm_analysis_port #(T)` | Producer (monitor, predictor) | Output — calls `write()` | Export or imp |
| `uvm_analysis_export #(T)` | Intermediary (FIFO, pass-through env) | Pass-through | Forwards to an imp |
| `uvm_analysis_imp #(T, C)` | Consumer (scoreboard, subscriber) | Input — implements `write()` | Source port |

**Mnemonic:** ports produce, exports/imps consume. Always:
`producer.port.connect(consumer.export_or_imp)`.

## Monitor anatomy

A complete monitor:

```systemverilog
class axi_monitor extends uvm_monitor;
    `uvm_component_utils(axi_monitor)
    virtual axi_if vif;
    uvm_analysis_port #(axi_item) ap;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ap = new("ap", this);                  // TLM ports use new(), not factory
        if (!uvm_config_db#(virtual axi_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "no axi_if")
    endfunction

    task run_phase(uvm_phase phase);
        forever begin
            axi_item item;
            // 1. Wait for protocol-defining event
            @(posedge vif.clk iff (vif.awvalid && vif.awready));
            // 2. Build transaction from sampled signals
            item = axi_item::type_id::create("item");
            item.addr = vif.awaddr;
            item.data = vif.wdata;
            item.we   = 1'b1;
            // 3. Broadcast
            ap.write(item);
        end
    endtask
endclass
```

Three steps, always:

1. **Recognize protocol.** Wait for the event that defines a complete
   transaction (handshake, packet boundary).
2. **Build transaction.** Sample signals into a fresh sequence item.
3. **Broadcast.** `ap.write(item)` to all connected consumers.

> **Cookbook §10.1 guideline**: the monitor must `type_id::create()` a
> fresh item every transaction. Reusing the same handle and modifying
> it would cause every connected consumer to see the same final value
> due to handle aliasing.

## Predictor pattern — proxy DUT

A predictor mirrors what the DUT *should* do, producing expected
transactions for the scoreboard to compare.

```systemverilog
class axi_predictor extends uvm_component;
    `uvm_component_utils(axi_predictor)
    uvm_analysis_port #(axi_item) ap_expected;
    uvm_analysis_imp #(axi_input_item, axi_predictor) input_imp;

    // Internal model state
    logic [31:0] mem [logic [31:0]];

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ap_expected = new("ap_expected", this);
        input_imp   = new("input_imp", this);
    endfunction

    // Called by env wiring up input monitor → predictor
    function void write(axi_input_item t);
        axi_item expected;
        expected = axi_item::type_id::create("expected");
        if (t.we) begin
            mem[t.addr] = t.data;
            expected.data = t.data;
        end else begin
            expected.data = mem.exists(t.addr) ? mem[t.addr] : '0;
        end
        expected.addr = t.addr;
        expected.we   = t.we;
        ap_expected.write(expected);    // → scoreboard.expected_fifo
    endfunction
endclass
```

The env wires: input-side monitor → predictor → scoreboard expected
side. Output-side monitor → scoreboard actual side.

Predictor patterns vary by complexity:

| Type | Use |
|---|---|
| **Stateless transform** | DUT performs algorithmic mapping (e.g., CRC computation) |
| **Stateful proxy** | DUT has memory/state (e.g., register file, cache) |
| **External tool** | Reference model in C, MATLAB, Python — DPI bridge |

## TLM analysis FIFO — decouple write-rate from read-rate

`uvm_tlm_analysis_fifo #(T)` exposes:
- `analysis_export` — input side (connects to a producer's `ap`).
- `get(item)` — output side, blocking.

```systemverilog
uvm_tlm_analysis_fifo #(my_item) act_fifo;
act_fifo = new("act_fifo", this);

// env connect_phase
monitor.ap.connect(sb.act_fifo.analysis_export);

// scoreboard run_phase
my_item item;
act_fifo.get(item);          // blocks until item available
```

Why not a plain `uvm_analysis_imp`? The imp's `write()` is a function
(zero time, non-blocking). If the consumer needs blocking operations
(file I/O, model queries, waiting), use the FIFO.

> **Cookbook §10**: standard scoreboard pattern uses two FIFOs (expected
> and actual). Never use `q[$]` directly — no blocking get, no size
> visibility.

## Dual-FIFO scoreboard — canonical

```systemverilog
class axi_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(axi_scoreboard)

    uvm_tlm_analysis_fifo #(axi_item) exp_fifo;
    uvm_tlm_analysis_fifo #(axi_item) act_fifo;

    int unsigned pass_count;
    int unsigned fail_count;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        exp_fifo = new("exp_fifo", this);
        act_fifo = new("act_fifo", this);
    endfunction

    task run_phase(uvm_phase phase);
        axi_item exp_item, act_item;
        forever begin
            exp_fifo.get(exp_item);
            act_fifo.get(act_item);
            if (!act_item.do_compare(exp_item, null)) begin
                `uvm_error("SB_MISMATCH", $sformatf(
                    "EXP: %s  ACT: %s",
                    exp_item.convert2string(),
                    act_item.convert2string()))
                fail_count++;
            end else begin
                pass_count++;
            end
        end
    endtask

    function void check_phase(uvm_phase phase);
        super.check_phase(phase);
        if (exp_fifo.size() != 0)
            `uvm_error("SB_LEFTOVER",
                $sformatf("%0d expected items unmatched", exp_fifo.size()))
        if (act_fifo.size() != 0)
            `uvm_error("SB_LEFTOVER",
                $sformatf("%0d actual items unmatched", act_fifo.size()))
        if (fail_count > 0)
            `uvm_error("SB_FAIL",
                $sformatf("%0d mismatches", fail_count))
    endfunction

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("SB", $sformatf("Pass=%0d Fail=%0d", pass_count, fail_count), UVM_NONE)
    endfunction
endclass
```

**The scoreboard does NOT raise an objection.** The test owns
raise/drop. If the scoreboard raised, the `forever` loop would prevent
the phase from ending.

## `uvm_in_order_comparator` — built-in alternative

For strictly in-order matching against `do_compare`:

```systemverilog
uvm_in_order_comparator #(my_item) cmp;
cmp = new("cmp", this);

// connect:
predictor.ap.connect(cmp.before_export);
monitor.ap.connect(cmp.after_export);
```

The comparator handles dual-FIFO bookkeeping internally. Reports
mismatches automatically. Use when:
- Strict in-order matching is correct for your protocol.
- Custom matching logic isn't needed.

Use the manual dual-FIFO pattern for: out-of-order, content-addressed
matching, multi-stream interleaving.

## `uvm_subscriber` — coverage-style consumer

`uvm_subscriber #(T)` automatically provides an `analysis_export`.
Subclass it and implement `write(T t)`:

```systemverilog
class axi_coverage extends uvm_subscriber #(axi_item);
    `uvm_component_utils(axi_coverage)

    axi_item trans;
    covergroup cg;
        cp_addr: coverpoint trans.addr[15:2];
        cp_we:   coverpoint trans.we;
        cx:      cross cp_addr, cp_we;
    endgroup

    function new(string name, uvm_component parent);
        super.new(name, parent);
        cg = new();
    endfunction

    function void write(axi_item t);
        trans = t;
        cg.sample();
    endfunction
endclass

// connect:
monitor.ap.connect(coverage.analysis_export);
```

## Multiple analysis imps on one scoreboard

When a scoreboard receives different transaction types from different
monitors, use `uvm_analysis_imp_decl`:

```systemverilog
`uvm_analysis_imp_decl(_input)
`uvm_analysis_imp_decl(_output)

class dual_sb extends uvm_scoreboard;
    `uvm_component_utils(dual_sb)

    uvm_analysis_imp_input  #(input_item,  dual_sb) input_imp;
    uvm_analysis_imp_output #(output_item, dual_sb) output_imp;

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        input_imp  = new("input_imp",  this);
        output_imp = new("output_imp", this);
    endfunction

    function void write_input (input_item  t); /* update reference */ endfunction
    function void write_output(output_item t); /* compare        */ endfunction
endclass
```

The suffix on `uvm_analysis_imp_decl` (`_input`, `_output`) becomes
the suffix on the `write_*` method name.

## Post-run phases for scoreboards

The cookbook recommends spreading scoreboard responsibilities across
clean-up phases:

| Phase | What the scoreboard does |
|---|---|
| `extract_phase` | Pull final statistics; check FIFO emptiness |
| `check_phase` | Decide pass/fail; `uvm_error` on issues |
| `report_phase` | Print summary; write CSV/JSON for CI |
| `final_phase` | Close files, free resources |

```systemverilog
function void extract_phase(uvm_phase phase);
    super.extract_phase(phase);
    n_leftover = exp_fifo.size() + act_fifo.size();
endfunction

function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    if (n_leftover != 0)
        `uvm_error("LEFTOVER", $sformatf("%0d unmatched", n_leftover))
endfunction

function void report_phase(uvm_phase phase);
    super.report_phase(phase);
    `uvm_info("SB", $sformatf(
        "Pass: %0d  Fail: %0d  Leftover: %0d",
        pass_count, fail_count, n_leftover), UVM_NONE)
endfunction
```

## Metric analyzer — coverage rollup

A metric analyzer collects coverage from subscribers and rolls up at
end-of-test:

```systemverilog
class metric_analyzer extends uvm_component;
    `uvm_component_utils(metric_analyzer)
    axi_coverage axi_cov;
    spi_coverage spi_cov;
    // ... env wires these handles ...

    function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info("COVERAGE", $sformatf(
            "AXI=%.1f%%  SPI=%.1f%%",
            axi_cov.cg.get_inst_coverage(),
            spi_cov.cg.get_inst_coverage()), UVM_NONE)
    endfunction
endclass
```

## Common pitfalls

- **Port→port instead of port→export.** Compiles, fails at end-of-elab.
- **Re-using one transaction handle in monitor.** All consumers see
  the same final state. Always `type_id::create("item")` fresh.
- **`uvm_analysis_imp::write()` blocking.** Imp write is a function —
  cannot consume time. Switch to FIFO if blocking is needed.
- **Scoreboard raises objection.** `forever` loop never exits;
  simulation deadlocks. Tests own objections.
- **Predictor input wired from output monitor.** The reference model
  needs the *input* to the DUT, not the output. Predictor input
  comes from the input-side monitor.
- **`field_*` macros for objects with handle members.** UVM-1.2's
  `do_compare` recursion through `uvm_field_object` is buggy for
  cyclic graphs. Hand-write `do_compare` for those.
- **`uvm_in_order_comparator` for out-of-order protocols.** Misses
  matches. Use dual-FIFO with associative-array indexing instead.

## Citations

- **Mentor Graphics UVM Cookbook**, *Analysis Connections* /
  *Monitor Component* / *Predictors* / *Scoreboards* /
  *Metric Analyzers* / *PostRunPhases* chapters.
- **Accellera UVM 1.2 §10** — analysis port / export / imp API,
  TLM analysis FIFO.

## See also

- `component-architecture.md` — wiring monitors and scoreboards in
  env connect_phase.
- `sequences-and-items.md` — `do_compare` / `do_copy` on the items
  that flow through these ports.
- `register-model.md` — register-based scoreboard pattern.
- `phasing-deep-dive.md` — extract / check / report / final phases.
