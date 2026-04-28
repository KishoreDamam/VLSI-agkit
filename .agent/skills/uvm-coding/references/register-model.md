# UVM Register Model (RAL)

> Register abstraction layer: reg_block, adapter, predictor, and register test sequences.

## RAL overview

```
Test / Sequence
      |
      v
uvm_reg_block  (register model — the "spec" in SV)
      |
      v
uvm_reg_map    (address map — offset of each register)
      |
      v
uvm_reg_adapter  (translate: reg_rw <-> bus transaction)
      |
      v
uvm_reg_predictor  (passive: update mirror from observed bus traffic)
      |
      v
Bus Sequencer / Agent (drives actual bus protocol)
```

---

## `uvm_reg_field`, `uvm_reg`, `uvm_reg_block`

```systemverilog
// --- Register field ---
class ctrl_reg extends uvm_reg;
    `uvm_object_utils(ctrl_reg)

    uvm_reg_field enable;   // bit 0
    uvm_reg_field mode;     // bits 2:1

    function new(string name = "ctrl_reg");
        super.new(name, 32, UVM_NO_COVERAGE);  // 32-bit register
    endfunction

    function void build();
        enable = uvm_reg_field::type_id::create("enable");
        mode   = uvm_reg_field::type_id::create("mode");
        // configure(parent, size, lsb_pos, access, volatile, reset, has_reset, ...)
        enable.configure(this, 1, 0, "RW", 0, 1'b0, 1, 1, 0);
        mode.configure(  this, 2, 1, "RW", 0, 2'b00, 1, 1, 0);
    endfunction
endclass

// --- Register block ---
class axi_reg_block extends uvm_reg_block;
    `uvm_object_utils(axi_reg_block)

    ctrl_reg    ctrl;
    uvm_reg_map axi_map;

    function new(string name = "axi_reg_block");
        super.new(name, UVM_NO_COVERAGE);
    endfunction

    function void build();
        axi_map = create_map("axi_map", 32'h0, 4, UVM_LITTLE_ENDIAN);

        ctrl = ctrl_reg::type_id::create("ctrl");
        ctrl.build();
        ctrl.configure(this);                       // no parent reg block for fields
        axi_map.add_reg(ctrl, 32'h0, "RW");        // offset 0x0

        lock_model();  // must call after all registers are added
    endfunction
endclass
```

---

## `uvm_reg_adapter` — translating between reg operations and bus transactions

The adapter converts between `uvm_reg_bus_op` (generic reg r/w) and the actual bus
sequence item (e.g., `axi_item`).

```systemverilog
class axi_reg_adapter extends uvm_reg_adapter;
    `uvm_object_utils(axi_reg_adapter)

    function new(string name = "axi_reg_adapter");
        super.new(name);
        supports_byte_enable = 0;
        provides_responses   = 0;
    endfunction

    // reg2bus: RAL wants to write/read — translate to bus item
    function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
        axi_item item = axi_item::type_id::create("item");
        item.addr = rw.addr;
        item.data = rw.data;
        item.we   = (rw.kind == UVM_WRITE) ? 1'b1 : 1'b0;
        return item;
    endfunction

    // bus2reg: monitor observed a transaction — update RAL mirror
    function void bus2reg(uvm_sequence_item bus_item,
                          ref uvm_reg_bus_op rw);
        axi_item item;
        if (!$cast(item, bus_item))
            `uvm_fatal("CAST", "bus2reg: item is not axi_item")
        rw.kind  = item.we ? UVM_WRITE : UVM_READ;
        rw.addr  = item.addr;
        rw.data  = item.data;
        rw.status = UVM_IS_OK;
    endfunction
endclass
```

**Gotcha:** both `reg2bus` and `bus2reg` must be implemented. `bus2reg` is called by the
predictor; omitting it means passive monitoring does not update the mirror.

---

## `uvm_reg_predictor` — passive mirror updates

```systemverilog
// In env build_phase:
uvm_reg_predictor #(axi_item) predictor;
predictor = uvm_reg_predictor#(axi_item)::type_id::create("predictor", this);

// In env connect_phase:
predictor.map     = reg_block.axi_map;
predictor.adapter = adapter;
monitor.ap.connect(predictor.bus_in);   // predictor receives all observed transactions
```

The predictor calls `adapter.bus2reg()` on each observed transaction and updates the
register model's mirror value automatically, keeping `reg.get_mirrored_value()` correct
even for writes the test did not initiate.

---

## Register test sequences

```systemverilog
// --- Write-readback test ---
task write_readback_test(axi_reg_block regs, uvm_reg_map map);
    uvm_status_e status;
    uvm_reg_data_t rdata;
    // Write a known pattern
    regs.ctrl.write(status, 32'hA5A5_A5A5, .map(map));
    assert(status == UVM_IS_OK);
    // Read back and compare
    regs.ctrl.read(status, rdata, .map(map));
    assert(status == UVM_IS_OK);
    if (rdata !== 32'hA5A5_A5A5)
        `uvm_error("RDK", $sformatf("Write-readback failed: got 0x%08h", rdata))
endtask

// --- Reset value check ---
task reset_value_check(axi_reg_block regs, uvm_reg_map map);
    uvm_status_e status;
    uvm_reg_data_t rdata;
    uvm_reg regs_arr[$];
    regs.get_registers(regs_arr);
    foreach (regs_arr[i]) begin
        regs_arr[i].read(status, rdata, .map(map));
        if (rdata !== regs_arr[i].get_reset())
            `uvm_error("RST", $sformatf("%s reset mismatch: got 0x%0h exp 0x%0h",
                regs_arr[i].get_name(), rdata, regs_arr[i].get_reset()))
    end
endtask
```

**UVM built-in register sequences:**
- `uvm_reg_hw_reset_seq` — checks all registers read back their reset values.
- `uvm_reg_bit_bash_seq` — walking-1s and walking-0s through all RW fields.
- `uvm_reg_access_seq` — write/readback for all RW registers.

```systemverilog
// Using built-in sequence:
uvm_reg_hw_reset_seq reset_seq = uvm_reg_hw_reset_seq::type_id::create("reset_seq");
reset_seq.model = env.reg_block;
reset_seq.start(env.agent.sqr);
```
