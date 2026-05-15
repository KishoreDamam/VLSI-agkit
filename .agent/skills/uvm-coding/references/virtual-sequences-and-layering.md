# Virtual Sequences & Layering

> Multi-agent coordination (virtual sequences) and protocol layering
> (translator sequences). Two distinct patterns often confused — this
> reference disentangles them.

## Two related but distinct problems

| Problem | Solution | Mechanism |
|---|---|---|
| One scenario drives multiple agents in coordinated time | **Virtual sequence** running on a virtual sequencer | Sequence runs on a sequencer that has no driver; spawns child sequences on real sequencers |
| One high-level protocol expressed in terms of a lower-level protocol | **Layering** (translator sequence) | High-level sequence items converted to low-level items by a translator that runs on the real sequencer |

Both involve a "sequence above a sequencer" — but they solve different
problems.

## Virtual sequences

### What they are

A virtual sequence is a sequence that doesn't directly send items to a
driver. Instead, it **starts other sequences on multiple sequencers**.

```
                  ┌─ apb_sqr  ──→ apb driver
                  │
virtual_seq ──────┼─ spi_sqr  ──→ spi driver
                  │
                  └─ uart_sqr ──→ uart driver
```

A virtual sequencer holds handles to all the agents' sequencers but
has no driver of its own. The virtual sequence executes coordinated
stimulus across all of them.

### Virtual sequencer

```systemverilog
class chip_virtual_sequencer extends uvm_sequencer;
    `uvm_component_utils(chip_virtual_sequencer)

    // Handles to real sequencers
    apb_sequencer  apb_sqr;
    spi_sequencer  spi_sqr;
    uart_sequencer uart_sqr;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
endclass
```

Constructed in the env's `build_phase`. Handles are assigned in the
env's `connect_phase`:

```systemverilog
function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    v_sqr.apb_sqr  = apb_agent.sqr;
    v_sqr.spi_sqr  = spi_agent.sqr;
    v_sqr.uart_sqr = uart_agent.sqr;
endfunction
```

### Virtual sequence

```systemverilog
class chip_init_vseq extends uvm_sequence;
    `uvm_object_utils(chip_init_vseq)
    `uvm_declare_p_sequencer(chip_virtual_sequencer)

    function new(string name = "chip_init_vseq");
        super.new(name);
    endfunction

    task body();
        apb_write_seq cfg_seq;
        spi_data_seq  data_seq;

        // Run APB config first
        cfg_seq = apb_write_seq::type_id::create("cfg_seq");
        cfg_seq.start(p_sequencer.apb_sqr, this);

        // Then run SPI data fork in parallel with UART
        fork
            begin
                data_seq = spi_data_seq::type_id::create("data_seq");
                data_seq.start(p_sequencer.spi_sqr, this);
            end
            begin
                uart_seq us = uart_seq::type_id::create("us");
                us.start(p_sequencer.uart_sqr, this);
            end
        join
    endtask
endclass
```

`` `uvm_declare_p_sequencer(T) `` gives you a typed `p_sequencer`
pointer (the actual virtual sequencer this is running on), so you can
access its agent-sequencer handles without casting.

### Recommended initialization

> Cookbook §10.1 / 9.x: pass the virtual sequencer at sequence start
> time, not via inheritance. Concrete pattern:

```systemverilog
// In the test:
task main_phase(uvm_phase phase);
    chip_init_vseq vseq;
    phase.raise_objection(this);
    vseq = chip_init_vseq::type_id::create("vseq");
    vseq.start(env.v_sqr);                    // start on virtual sequencer
    phase.drop_objection(this);
endtask
```

The child sequences receive their real sequencer via `start(real_sqr,
this)`. The `this` parameter sets the parent sequence — needed for
objection propagation up to the virtual sequencer.

### Cookbook checks for virtual sequences

- **Check for null sequencer handles before starting child sequences.**
  If the env didn't connect a handle, you get a confusing null-pointer
  error. Check upfront:
  ```systemverilog
  if (p_sequencer.spi_sqr == null) `uvm_fatal("VSEQ", "spi_sqr null")
  ```
- **Never raise objections inside a virtual sequence.** Virtual
  sequences whose `m_sequencer` is null don't propagate. Raise in the
  test instead.
- **Don't directly consume time in a virtual sequence except via
  child sequences.** A virtual sequence is a *coordinator*; it should
  start child sequences, not drive timing itself.

## Layering / translator sequences

### The problem

A protocol stack: high-level operations expressed in low-level
transactions. Example:

```
ethernet frames  → AXI4 bursts → AXI4 beats
```

Or:

```
register reads/writes → APB transactions
```

You want one sequence to express "issue 100 Ethernet frames"; under
the hood, each frame translates to many AXI4 beats.

### Architecture

```
                       ┌──────────────────────────┐
                       │ High-level sequence       │
                       │ (Ethernet frames)         │
                       └────────┬─────────────────┘
                                │ frame items
                                ▼
                       ┌──────────────────────────┐
                       │ Protocol agent / driver  │
                       │ (translator)             │  ← receives frame items
                       └────────┬─────────────────┘
                                │ starts low-level sequence
                                ▼
                       ┌──────────────────────────┐
                       │ Low-level sequencer      │
                       │ (AXI4 sequencer)         │
                       └────────┬─────────────────┘
                                │ AXI4 items
                                ▼
                       ┌──────────────────────────┐
                       │ AXI4 driver              │
                       └──────────────────────────┘
```

The **protocol agent** has a driver that, instead of poking pins,
*starts a sequence* on the next layer's sequencer. Each "transaction"
at the upper level expands into many at the lower level.

### Internal vs external protocol agent

| Style | Where the translator lives | When to use |
|---|---|---|
| **Internal** | Translator sequence runs *on the same sequencer* as the high-level | Simple stack, one protocol pair |
| **External** | Translator is its own agent with a driver-like component | Multi-stage stack, reusable across testbenches |

The cookbook recommends external for production VIPs.

### Layered driver pattern

```systemverilog
// Protocol agent's "driver" — actually a translator
class eth_translator extends uvm_driver #(eth_frame);
    `uvm_component_utils(eth_translator)

    uvm_sequencer #(axi_seq_item) axi_sqr;   // handle to next layer

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        // env wires axi_sqr to the AXI agent's sequencer
    endfunction

    task run_phase(uvm_phase phase);
        eth_frame frame;
        forever begin
            seq_item_port.get_next_item(frame);
            translate_and_send(frame);
            seq_item_port.item_done();
        end
    endtask

    task translate_and_send(eth_frame frame);
        eth_to_axi_seq seq;
        seq = eth_to_axi_seq::type_id::create("seq");
        seq.frame = frame;
        seq.start(axi_sqr);
    endtask
endclass
```

The translator sequence:

```systemverilog
class eth_to_axi_seq extends uvm_sequence #(axi_seq_item);
    `uvm_object_utils(eth_to_axi_seq)

    eth_frame frame;

    task body();
        axi_seq_item beat;
        foreach (frame.payload[i]) begin
            beat = axi_seq_item::type_id::create("beat");
            start_item(beat);
            assert(beat.randomize() with {
                data == frame.payload[i];
                we   == 1'b1;
            }) else `uvm_fatal("RAND", "axi beat randomize failed")
            finish_item(beat);
        end
    endtask
endclass
```

### Analysis path through a layered stack

The monitor path is the inverse of the driver path:

```
AXI monitor → builds AXI items → broadcasts on AXI ap
                                      │
                                      ▼
                            eth_recognizer (subscriber)
                                      │
                                      ▼
                            builds eth_frame → eth ap
                                      │
                                      ▼
                            Top-level scoreboard
```

The recognizer subscribes to AXI items and reassembles Ethernet
frames. Each layer's monitor produces items at its abstraction level
for that layer's scoreboard.

## API / Worker / Virtual sequence hierarchy

A three-tier organization the cookbook recommends:

| Tier | Role | Example |
|---|---|---|
| **API sequences** | Lowest layer — atomic operations | `register_write`, `register_read` |
| **Worker sequences** | Middle layer — multi-step procedures composed of API sequences | `program_dma`, `reset_chip` |
| **Virtual sequences** | Top — full test scenarios across agents | `boot_sequence`, `stress_test` |

This hierarchy makes complex tests readable: virtual seq calls worker
seqs, which call API seqs.

## Common pitfalls

- **Virtual sequence forgotten the second arg to `start`.** `seq.start(sqr)` is
  fine for a top-level sequence but `start(sqr, this)` is required when
  one sequence starts another to preserve parentage and objection
  propagation.
- **`p_sequencer` accessed without `uvm_declare_p_sequencer`.** Without
  the macro, `p_sequencer` is `uvm_sequencer` (base type) and you
  can't access agent-specific handles. Always use the macro for typed
  access.
- **Virtual sequencer registered as `uvm_component_param_utils`.** Use
  plain `uvm_component_utils` — virtual sequencers are rarely
  parameterized.
- **Driver-based translator missing `item_done()`.** Same trap as any
  driver — the upstream sequence stalls.
- **Layered analysis path that just forwards items.** The whole point of
  layering is *aggregation* — the layer-N+1 monitor should produce
  N+1-level items, not relay N-level items.
- **API sequences that call worker sequences.** Inverted layering.
  API is the bottom; worker uses API; virtual uses worker.

## Citations

- **Mentor Graphics UVM Cookbook**, *Sequences/Virtual*, *Sequences/Layering*,
  *Sequences/Hierarchy* — virtual sequence patterns, layering
  architecture, API/worker/virtual hierarchy.
- **Cookbook §4.6** — null-sequencer-handle check guideline.

## See also

- `sequences-and-items.md` — base sequence patterns.
- `component-architecture.md` — virtual sequencer in the env hierarchy.
- `objections-deep-dive.md` — why virtual sequences shouldn't raise
  objections.
- `analysis-ports-and-scoreboards.md` — the layered analysis path.
