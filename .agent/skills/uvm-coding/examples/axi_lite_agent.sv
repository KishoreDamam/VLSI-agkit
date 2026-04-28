// axi_lite_agent.sv -- Complete AXI-Lite UVM agent
//
// Demonstrates:
//   - uvm_sequence_item with rand fields and constraints
//   - uvm_config object carrying VIF and active/passive enum
//   - uvm_driver: config_db VIF retrieval, get_next_item/item_done loop
//   - uvm_monitor: sample completed transactions, write to analysis port
//   - uvm_agent: active/passive guard, factory create, seq_item_port wiring
//
// AXI-Lite protocol summary:
//   Write: AWVALID/AWREADY (addr), WVALID/WREADY (data), BVALID/BREADY (resp)
//   Read:  ARVALID/ARREADY (addr), RVALID/RREADY (data+resp)

`ifndef AXI_LITE_AGENT_SV
`define AXI_LITE_AGENT_SV

// ---------------------------------------------------------------------------
// Interface -- must be instantiated in the top-level testbench module
// ---------------------------------------------------------------------------
interface axi_lite_if #(parameter int AW = 32, parameter int DW = 32) (
    input logic clk,
    input logic rst_n
);
    // Write address channel
    logic [AW-1:0] awaddr;
    logic          awvalid;
    logic          awready;
    // Write data channel
    logic [DW-1:0] wdata;
    logic [DW/8-1:0] wstrb;
    logic          wvalid;
    logic          wready;
    // Write response channel
    logic [1:0]    bresp;
    logic          bvalid;
    logic          bready;
    // Read address channel
    logic [AW-1:0] araddr;
    logic          arvalid;
    logic          arready;
    // Read data channel
    logic [DW-1:0] rdata;
    logic [1:0]    rresp;
    logic          rvalid;
    logic          rready;
endinterface

// ---------------------------------------------------------------------------
// Sequence item
// ---------------------------------------------------------------------------
class axi_lite_seq_item extends uvm_sequence_item;
    `uvm_object_utils(axi_lite_seq_item)

    rand logic [31:0] addr;
    rand logic [31:0] data;
    rand logic        we;    // 1=write, 0=read

    // AXI-Lite: 4-byte aligned addresses only
    constraint c_align { addr[1:0] == 2'b00; }
    // Keep to lower 64 KB; tests can extend or override this constraint
    constraint c_range  { addr inside {[32'h0000_0000 : 32'h0000_FFFC]}; }

    logic [1:0] resp;  // response from DUT -- filled by driver, not randomized

    function new(string name = "axi_lite_seq_item");
        super.new(name);
    endfunction

    function string convert2string();
        return $sformatf("[axi_lite] %s addr=0x%08h data=0x%08h resp=%0b",
                         we ? "WR" : "RD", addr, data, resp);
    endfunction
endclass

// ---------------------------------------------------------------------------
// Config object -- carries VIF handle and active/passive mode
// ---------------------------------------------------------------------------
class axi_lite_config extends uvm_object;
    `uvm_object_utils(axi_lite_config)

    // UVM_ACTIVE creates driver+sequencer; UVM_PASSIVE monitor-only mode
    uvm_active_passive_enum is_active = UVM_ACTIVE;

    // Virtual interface handle -- set by the top-level testbench via config_db
    virtual axi_lite_if vif;

    function new(string name = "axi_lite_config");
        super.new(name);
    endfunction
endclass

// ---------------------------------------------------------------------------
// Driver -- drives AXI-Lite write and read transactions onto the interface
// ---------------------------------------------------------------------------
class axi_lite_driver extends uvm_driver #(axi_lite_seq_item);
    `uvm_component_utils(axi_lite_driver)

    axi_lite_config cfg;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    // build_phase: retrieve config object (which holds the VIF) from config_db
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db #(axi_lite_config)::get(this, "", "cfg", cfg))
            `uvm_fatal("NOCFG", {"axi_lite_config not found for ", get_full_name()})
    endfunction

    // run_phase: standard get_next_item / item_done driver loop.
    // item_done() MUST be called every iteration -- omitting it stalls the sequence.
    task run_phase(uvm_phase phase);
        init_signals();
        @(posedge cfg.vif.clk iff cfg.vif.rst_n);  // wait for reset deassertion

        forever begin
            seq_item_port.get_next_item(req);   // blocks until sequence provides item
            if (req.we)
                drive_write(req);
            else
                drive_read(req);
            seq_item_port.item_done();           // release the sequence
        end
    endtask

    task init_signals();
        cfg.vif.awvalid <= 1'b0;
        cfg.vif.wvalid  <= 1'b0;
        cfg.vif.bready  <= 1'b0;
        cfg.vif.arvalid <= 1'b0;
        cfg.vif.rready  <= 1'b0;
    endtask

    // AXI-Lite write: present address and data simultaneously.
    // Both channels must complete handshakes before response is issued.
    task drive_write(axi_lite_seq_item item);
        @(posedge cfg.vif.clk);
        cfg.vif.awaddr  <= item.addr;
        cfg.vif.awvalid <= 1'b1;
        cfg.vif.wdata   <= item.data;
        cfg.vif.wstrb   <= 4'hF;
        cfg.vif.wvalid  <= 1'b1;

        // Wait for write address handshake (awvalid && awready)
        @(posedge cfg.vif.clk iff cfg.vif.awready);
        cfg.vif.awvalid <= 1'b0;

        // Wait for write data handshake (wvalid && wready)
        @(posedge cfg.vif.clk iff cfg.vif.wready);
        cfg.vif.wvalid <= 1'b0;

        // Accept write response
        cfg.vif.bready <= 1'b1;
        @(posedge cfg.vif.clk iff cfg.vif.bvalid);
        item.resp = cfg.vif.bresp;
        cfg.vif.bready <= 1'b0;
    endtask

    // AXI-Lite read: present address, wait for handshake, accept read data.
    task drive_read(axi_lite_seq_item item);
        @(posedge cfg.vif.clk);
        cfg.vif.araddr  <= item.addr;
        cfg.vif.arvalid <= 1'b1;

        @(posedge cfg.vif.clk iff cfg.vif.arready);
        cfg.vif.arvalid <= 1'b0;

        cfg.vif.rready  <= 1'b1;
        @(posedge cfg.vif.clk iff cfg.vif.rvalid);
        item.data = cfg.vif.rdata;
        item.resp = cfg.vif.rresp;
        cfg.vif.rready <= 1'b0;
    endtask
endclass

// ---------------------------------------------------------------------------
// Monitor -- samples completed AXI-Lite transactions, broadcasts via ap
// ---------------------------------------------------------------------------
class axi_lite_monitor extends uvm_monitor;
    `uvm_component_utils(axi_lite_monitor)

    axi_lite_config cfg;
    uvm_analysis_port #(axi_lite_seq_item) ap;  // connect to scoreboard/coverage

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // TLM ports use new() -- they are not UVM factory-managed components
        ap = new("ap", this);
        if (!uvm_config_db #(axi_lite_config)::get(this, "", "cfg", cfg))
            `uvm_fatal("NOCFG", {"axi_lite_config not found for ", get_full_name()})
    endfunction

    task run_phase(uvm_phase phase);
        // Fork separate threads for write and read monitoring
        fork
            monitor_writes();
            monitor_reads();
        join_none
    endtask

    // Capture write transactions when write response completes (bvalid+bready)
    task monitor_writes();
        forever begin
            axi_lite_seq_item item;
            @(posedge cfg.vif.clk iff (cfg.vif.bvalid && cfg.vif.bready));
            item      = axi_lite_seq_item::type_id::create("mon_wr");
            item.we   = 1'b1;
            item.addr = cfg.vif.awaddr;
            item.data = cfg.vif.wdata;
            item.resp = cfg.vif.bresp;
            `uvm_info("MON_WR", item.convert2string(), UVM_HIGH)
            ap.write(item);   // broadcasts to all connected analysis exports
        end
    endtask

    // Capture read transactions when read data is accepted (rvalid+rready)
    task monitor_reads();
        forever begin
            axi_lite_seq_item item;
            @(posedge cfg.vif.clk iff (cfg.vif.rvalid && cfg.vif.rready));
            item      = axi_lite_seq_item::type_id::create("mon_rd");
            item.we   = 1'b0;
            item.addr = cfg.vif.araddr;
            item.data = cfg.vif.rdata;
            item.resp = cfg.vif.rresp;
            `uvm_info("MON_RD", item.convert2string(), UVM_HIGH)
            ap.write(item);
        end
    endtask
endclass

// ---------------------------------------------------------------------------
// Sequencer -- standard parameterized sequencer; no custom logic needed
// ---------------------------------------------------------------------------
typedef uvm_sequencer #(axi_lite_seq_item) axi_lite_sequencer;

// ---------------------------------------------------------------------------
// Agent -- assembles config, driver, monitor, sequencer
// ---------------------------------------------------------------------------
class axi_lite_agent extends uvm_agent;
    `uvm_component_utils(axi_lite_agent)

    axi_lite_config    cfg;
    axi_lite_driver    drv;
    axi_lite_monitor   mon;
    axi_lite_sequencer sqr;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        // Allow test/env to provide config; create a default if none present
        if (!uvm_config_db #(axi_lite_config)::get(this, "", "cfg", cfg)) begin
            `uvm_info("AGENT", "No config found -- creating default", UVM_MEDIUM)
            cfg = axi_lite_config::type_id::create("cfg");
        end

        // Push config to children (driver and monitor retrieve it by "cfg")
        uvm_config_db #(axi_lite_config)::set(this, "*", "cfg", cfg);

        // Monitor is always created regardless of active/passive mode
        mon = axi_lite_monitor::type_id::create("mon", this);

        // Driver and sequencer only in active mode
        if (cfg.is_active == UVM_ACTIVE) begin
            drv = axi_lite_driver::type_id::create("drv", this);
            sqr = axi_lite_sequencer::type_id::create("sqr", this);
        end
    endfunction

    function void connect_phase(uvm_phase phase);
        // seq_item_port (on driver) connects to seq_item_export (on sequencer)
        // This wires the sequencer output to the driver input
        if (cfg.is_active == UVM_ACTIVE)
            drv.seq_item_port.connect(sqr.seq_item_export);
    endfunction
endclass

`endif // AXI_LITE_AGENT_SV
