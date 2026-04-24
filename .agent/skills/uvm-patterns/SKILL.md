---
name: uvm-patterns
description: UVM methodology, components, and verification patterns.
---

# UVM Patterns

> Universal Verification Methodology for SystemVerilog testbenches.

---

## UVM Architecture

```
                 ┌─────────────┐
                 │    Test     │
                 └──────┬──────┘
                        │
                 ┌──────▼──────┐
                 │ Environment │
                 │ ┌─────────┐ │
                 │ │  Agent  │ │
                 │ │ Sqr/Drv │ │
                 │ │ Monitor │ │
                 │ └─────────┘ │
                 │ ┌─────────┐ │
                 │ │Scorebrd │ │
                 │ └─────────┘ │
                 └──────┬──────┘
                        │
                 ┌──────▼──────┐
                 │     DUT     │
                 └─────────────┘
```

---

## Component Templates

### Sequence Item

```systemverilog
class my_item extends uvm_sequence_item;
    `uvm_object_utils(my_item)
    
    rand bit [31:0] addr;
    rand bit [31:0] data;
    rand bit        write;
    
    constraint c_addr { addr < 32'h1000; }
    
    function new(string name = "my_item");
        super.new(name);
    endfunction
    
    function string convert2string();
        return $sformatf("addr=0x%08h data=0x%08h %s",
                        addr, data, write ? "WR" : "RD");
    endfunction
endclass
```

### Sequence

```systemverilog
class my_sequence extends uvm_sequence #(my_item);
    `uvm_object_utils(my_sequence)
    
    function new(string name = "my_sequence");
        super.new(name);
    endfunction
    
    task body();
        repeat (10) begin
            `uvm_do_with(req, { addr < 32'h100; })
        end
    endtask
endclass
```

### Driver

```systemverilog
class my_driver extends uvm_driver #(my_item);
    `uvm_component_utils(my_driver)
    
    virtual my_if vif;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "VIF not set")
    endfunction
    
    task run_phase(uvm_phase phase);
        forever begin
            seq_item_port.get_next_item(req);
            drive(req);
            seq_item_port.item_done();
        end
    endtask
    
    task drive(my_item item);
        @(posedge vif.clk);
        vif.addr  <= item.addr;
        vif.data  <= item.data;
        vif.valid <= 1'b1;
        @(posedge vif.clk);
        while (!vif.ready) @(posedge vif.clk);
        vif.valid <= 1'b0;
    endtask
endclass
```

### Monitor

```systemverilog
class my_monitor extends uvm_monitor;
    `uvm_component_utils(my_monitor)
    
    virtual my_if vif;
    uvm_analysis_port #(my_item) ap;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ap = new("ap", this);
        if (!uvm_config_db#(virtual my_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "VIF not set")
    endfunction
    
    task run_phase(uvm_phase phase);
        forever begin
            my_item item = my_item::type_id::create("item");
            @(posedge vif.clk);
            if (vif.valid && vif.ready) begin
                item.addr = vif.addr;
                item.data = vif.data;
                ap.write(item);
            end
        end
    endtask
endclass
```

### Agent

```systemverilog
class my_agent extends uvm_agent;
    `uvm_component_utils(my_agent)
    
    my_driver    driver;
    my_sequencer sequencer;
    my_monitor   monitor;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        monitor = my_monitor::type_id::create("monitor", this);
        if (get_is_active() == UVM_ACTIVE) begin
            driver = my_driver::type_id::create("driver", this);
            sequencer = my_sequencer::type_id::create("sequencer", this);
        end
    endfunction
    
    function void connect_phase(uvm_phase phase);
        if (get_is_active() == UVM_ACTIVE)
            driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction
endclass
```

---

## Scoreboard

```systemverilog
class my_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(my_scoreboard)
    
    uvm_analysis_imp #(my_item, my_scoreboard) ap;
    my_item expected_q[$];
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        ap = new("ap", this);
    endfunction
    
    function void write(my_item item);
        if (expected_q.size() > 0) begin
            my_item exp = expected_q.pop_front();
            if (item.data != exp.data)
                `uvm_error("MISMATCH", $sformatf(
                    "Got %h, expected %h", item.data, exp.data))
        end
    endfunction
endclass
```

---

## Coverage

```systemverilog
class my_coverage extends uvm_subscriber #(my_item);
    `uvm_component_utils(my_coverage)
    
    covergroup cg;
        cp_addr: coverpoint trans.addr[7:0];
        cp_write: coverpoint trans.write;
        cx_addr_write: cross cp_addr, cp_write;
    endgroup
    
    my_item trans;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        cg = new();
    endfunction
    
    function void write(my_item t);
        trans = t;
        cg.sample();
    endfunction
endclass
```

---

## Best Practices

| Practice | Why |
|----------|-----|
| Use factory | Enables overrides |
| Use config_db | Flexible configuration |
| Raise/drop objections | Control simulation end |
| Use `uvm_info` | Consistent messaging |
| Coverage-driven | Completeness metric |
