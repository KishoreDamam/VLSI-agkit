# Two-Kingdoms — HDL/Testbench Domain Split for Emulation

> A modern testbench architecture pattern that separates **timed**
> (HDL-domain) and **untimed** (testbench-domain) code so the testbench
> can run on emulation hardware. The cookbook calls this the "Two
> Kingdoms" methodology.

## Why split

Standard UVM testbenches mix:

- **Timed** code: drivers using `@(posedge clk)`, monitors sampling
  signals, BFM tasks that consume cycles.
- **Untimed** code: sequence bodies, scoreboards, RAL operations,
  randomization, configuration.

Emulators (Veloce, Palladium, ZeBu, Protium) only execute synthesizable
HDL. Anything non-synthesizable — including most class-based UVM code
— runs on the host workstation, communicating with the emulator via a
slow PCIe link.

If timed and untimed code are interleaved cycle-by-cycle, the host has
to acknowledge every cycle → emulation runs at workstation speed →
defeats the point of emulation.

**Two-Kingdoms** separates them so the emulator can run thousands of
HDL cycles between testbench callouts.

## The architecture

```
        ┌─────────────────────────────────────────┐
        │   Testbench Domain (host, untimed)      │
        │                                          │
        │   Test → Sequences → Scoreboards         │
        │           │                              │
        │           │ task calls into BFM proxies  │
        │           ▼                              │
        │   Driver/Monitor "proxy" classes         │
        │   (class-based, untimed)                 │
        └────────────────┬─────────────────────────┘
                          │
                          │ Task-based interface
                          │ (function calls + simple types)
                          ▼
        ┌─────────────────────────────────────────┐
        │   HDL Domain (emulator, timed)           │
        │                                          │
        │   BFM modules / interfaces (synthesizable)│
        │   that touch the DUT pins                │
        │   - Driver BFM (timed)                   │
        │   - Monitor BFM (timed)                  │
        │   - Clock, reset gen                     │
        │   - DUT                                  │
        └─────────────────────────────────────────┘
```

The boundary is a **set of task/function calls** between the two
domains. Each call is one round-trip across the host↔emulator link, so
the call rate determines the emulation speedup. Per-transaction calls
are fine (~100s of cycles between calls); per-cycle would not be.

## Rules

1. **Two top-level modules.** One `hdl_top` instantiates the DUT,
   BFMs, clock/reset; one `tb_top` instantiates the UVM testbench.
   `vsim hdl_top tb_top` runs both.
2. **No class types in the HDL domain.** Everything in `hdl_top` is
   module-based, synthesizable.
3. **No `@(...)` in the testbench domain.** Time consumption happens
   only via BFM task calls.
4. **No cross-domain hierarchical references.** The testbench cannot
   read `hdl_top.dut.something`; communication is via the BFM proxy
   interface only.
5. **Communication via simple types only.** Pass `logic [N-1:0]`,
   structs of basic types. No class handles, no queues, no associative
   arrays across the boundary.

## Driver split

### Original (single-domain) driver

```systemverilog
class apb_driver extends uvm_driver #(apb_item);
    `uvm_component_utils(apb_driver)
    virtual apb_if vif;

    task run_phase(uvm_phase phase);
        apb_item item;
        forever begin
            seq_item_port.get_next_item(item);
            @(posedge vif.pclk);             // ← timed code
            vif.psel  <= 1'b1;
            vif.paddr <= item.addr;
            // ... drive sequence ...
            seq_item_port.item_done();
        end
    endtask
endclass
```

### Two-Kingdoms driver — proxy + BFM

**Testbench-domain proxy** (untimed):

```systemverilog
class apb_driver_proxy extends uvm_driver #(apb_item);
    `uvm_component_utils(apb_driver_proxy)

    virtual apb_driver_bfm bfm;            // virtual interface to BFM

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual apb_driver_bfm)::get(this, "", "bfm", bfm))
            `uvm_fatal("BFM", "no BFM handle")
    endfunction

    task run_phase(uvm_phase phase);
        apb_item item;
        forever begin
            seq_item_port.get_next_item(item);
            // One task call across the domain boundary
            bfm.drive(item.addr, item.data, item.we);
            seq_item_port.item_done();
        end
    endtask
endclass
```

**HDL-domain BFM** (timed, synthesizable):

```systemverilog
interface apb_driver_bfm (input pclk, output logic psel,
                          output logic [31:0] paddr,
                          output logic [31:0] pwdata,
                          /* etc */);

    task automatic drive(input [31:0] addr,
                          input [31:0] data,
                          input        we);
        @(posedge pclk);
        psel   <= 1'b1;
        paddr  <= addr;
        pwdata <= data;
        // ... full APB sequence ...
        @(posedge pclk);
        psel   <= 1'b0;
    endtask

endinterface
```

The proxy class is **untimed**: `bfm.drive()` is a single task call
that crosses into the HDL domain. The BFM consumes whatever cycles the
protocol requires; the proxy is blocked for that wall time but
performs no cycle-by-cycle handshakes.

## Monitor split

Same pattern in reverse.

**HDL-domain monitor BFM** samples signals and calls back into the
testbench:

```systemverilog
interface apb_monitor_bfm (input pclk, input psel, input penable,
                            input [31:0] paddr, input [31:0] pwdata, ...);

    apb_monitor_proxy proxy;     // handle into testbench domain

    initial wait (proxy != null);    // testbench domain assigns this

    always @(posedge pclk) begin
        if (psel && penable) begin
            proxy.notify_transaction(paddr, pwdata, /* etc */);
        end
    end
endinterface
```

**Testbench-domain monitor proxy** receives the callback:

```systemverilog
class apb_monitor_proxy extends uvm_monitor;
    `uvm_component_utils(apb_monitor_proxy)
    uvm_analysis_port #(apb_item) ap;

    function void notify_transaction(logic [31:0] addr,
                                     logic [31:0] data,
                                     ...);
        apb_item item = apb_item::type_id::create("item");
        item.addr = addr;
        item.data = data;
        ap.write(item);
    endfunction
endclass
```

The proxy registers itself with the BFM at start-of-simulation. The
BFM calls `proxy.notify_transaction()` directly (untimed function
call) from inside its always block.

## Virtual interface binding

```systemverilog
// hdl_top
module hdl_top;
    logic pclk;
    apb_driver_bfm  drv_bfm (.pclk, /* ... */);
    apb_monitor_bfm mon_bfm (.pclk, /* ... */);
    dut u_dut       (/* ... */);

    initial begin
        uvm_config_db#(virtual apb_driver_bfm)::set(
            null, "uvm_test_top.env.apb_agent.drv", "bfm", drv_bfm);
        uvm_config_db#(virtual apb_monitor_bfm)::set(
            null, "uvm_test_top.env.apb_agent.mon", "bfm", mon_bfm);
    end
endmodule

// tb_top
module tb_top;
    initial run_test();
endmodule
```

## Clock and reset

Clock and reset generation **must** stay in the HDL domain.
Testbench-domain `#delay` would not synthesize.

```systemverilog
module hdl_top;
    logic clk, rst_n;
    initial begin
        clk = 0; forever #5 clk = ~clk;     // synthesizable on emulator
    end
    initial begin
        rst_n = 0; #50 rst_n = 1;
    end
    // BFMs and DUT below
endmodule
```

## What stays in the testbench domain

- Sequences (untimed; they call into BFMs via the driver port).
- Scoreboards (call functions on the analysis FIFOs; no `@`).
- RAL register reads/writes (each calls into the bus BFM).
- Coverage collection (sampled when transactions arrive).
- Configuration, randomization.

## What stays in the HDL domain

- DUT.
- Clock/reset generators.
- Interfaces and BFM tasks (the only timed code).
- Assertions (SVA — synthesizable subset).

## Migration path from a regular UVM testbench

1. Identify the timed boundary in each driver/monitor (the `@(...)`
   line).
2. Move everything after that boundary into a BFM interface.
3. Replace the timed loop in the driver with a single BFM task call.
4. Replace the sampling block in the monitor with a BFM-side
   `always` that calls back into the proxy.
5. Move clock/reset to `hdl_top`.
6. Use `vsim hdl_top tb_top` to start both modules.

Most UVM Verification IP from vendors now ships with two-kingdoms-ready
structure (often called "split" or "BFM-based" drivers).

## When you don't need two-kingdoms

- Pure simulation projects: emulation is not in scope.
- VIP that will never run on an emulator.
- Designs small enough that simulation is fast enough.

Even so, the split has *side benefits*:
- Driver code that runs faster (fewer SV `@` events).
- Monitor code that's cleaner (sampling logic separated from
  bookkeeping).
- Easier to swap RTL DUT for FPGA prototype later.

## Common pitfalls

- **Class types in the BFM interface.** Breaks synthesizability. Use
  only simple types in the boundary.
- **`@` in the proxy class.** Defeats the split — time consumption
  drags the host back into per-cycle.
- **Calling BFM tasks before `uvm_config_db::get` returns.** Race in
  `build_phase` vs `run_phase`. Always check `bfm != null` before use.
- **Hierarchical references from testbench to HDL.** Some simulators
  allow it; emulators don't. The split must be strict.
- **Forgetting `automatic` on the BFM tasks.** Static tasks shared
  across BFM instances cause cross-instance corruption.

## Citations

- **Mentor Graphics UVM Cookbook**, *Two Kingdoms* chapter — full
  methodology with APB + SPI worked examples.
- **Veloce / Palladium / ZeBu emulator user guides** — host-emulator
  communication overhead measurements.

## See also

- `component-architecture.md` — virtual interface binding via
  config_db (Two-Kingdoms uses the same mechanism with BFM interfaces
  instead of raw interfaces).
- `analysis-ports-and-scoreboards.md` — monitor proxy + analysis port
  flow.
