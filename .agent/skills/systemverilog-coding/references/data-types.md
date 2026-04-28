# Data Types Reference — SystemVerilog

## logic vs reg vs wire: the definitive rule

In SystemVerilog, `logic` replaces both `reg` and `wire` for almost all RTL use cases.

### The single rule

> **Use `logic` for all RTL signals. Never use `reg` or `wire` in new SystemVerilog code
> unless you need explicit net semantics (wired-AND/OR) or are instantiating a legacy
> Verilog-2001 module that requires `wire` on a port.**

| Context | Correct type | Reason |
|---|---|---|
| `always_ff` output | `logic` | Single driver; compiler enforces it |
| `always_comb` output | `logic` | Single driver; no net needed |
| `assign` (continuous) | `logic` | Single driver; `assign` creates a driver |
| Module output port | `logic` | Same rule; `logic` drives its own port |
| Module input port | `logic` | Inputs are always implicitly nets; `logic` works |
| Tri-state / wired-OR | `wire` | Must use net type for multiple drivers |
| Legacy module port connection | `wire` | Some tools require net at module boundary |

### Why `reg` is confusing and retired

In Verilog-2001, `reg` means "assigned procedurally" — it does **not** mean a flip-flop.
A `reg` can be purely combinational if driven by an `always @(*)` block. This naming
causes the common mistake of guessing that `reg` implies storage.

SystemVerilog replaced this split with `logic`, which:
- Is a 4-state type (0, 1, X, Z) like `reg`.
- Can be driven by `always_ff`, `always_comb`, `assign`, or a port.
- The compiler rejects multiple `always_*` drivers on the same `logic` signal.

### Migration checklist (Verilog-2001 → SystemVerilog)

- [ ] Replace all `reg` with `logic`.
- [ ] Replace all `wire` with `logic`, except wired nets and legacy port connections.
- [ ] Replace `always @(posedge clk)` with `always_ff @(posedge clk or negedge rst_n)`.
- [ ] Replace `always @(*)` with `always_comb`.
- [ ] Replace `always @(...)` explicit sensitivity lists with `always_comb` or `always_ff`.

---

## Packed vs Unpacked arrays and types

### Packed dimensions (contiguous bit-vector)

Packed dimensions precede the variable name. They form a contiguous bit vector and are
synthesizable.

```systemverilog
logic [7:0]  byte_val;        // 8-bit packed
logic [3:0][7:0] byte_array;  // 4 bytes packed, 32 bits total
```

Access: `byte_array[2]` gives `byte_array[23:16]` (bit slice, contiguous).

### Unpacked dimensions (array of elements)

Unpacked dimensions follow the variable name. Elements are independent; synthesis support
varies by tool.

```systemverilog
logic [7:0] mem [0:255];      // 256-element unpacked array of bytes
logic       flags [7:0];      // 8-element unpacked array of single bits
```

### When to use which

| Use case | Recommendation |
|---|---|
| Bus or data path (synthesizable) | Packed — forms a single bit vector |
| Register file, ROM, RAM model | Unpacked of packed (`logic [31:0] rf [0:31]`) |
| Verification structures | Unpacked OK; synthesis not required |
| Struct fields | Packed struct for hardware; unpacked for TB-only |

---

## Structs and Unions

### Packed struct (synthesizable)

All fields are concatenated into a single bit vector (MSB-first, top field leftmost).
Total bit width must be computable at elaboration time.

```systemverilog
typedef struct packed {
    logic [3:0]  opcode;
    logic [11:0] address;
    logic [15:0] data;
} instruction_t;  // 32 bits total

instruction_t instr;
// Slice access:  instr.opcode, instr[31:28] — same bits
```

Gotchas:
- Fields inside a packed struct must all be packed types (no unpacked arrays inside).
- Endianness of struct packing: first field declared is the MSB. This is language-defined
  (IEEE 1800-2017 §7.4.1).
- Mixed-endian sub-fields (`[0:7]` vs `[7:0]`) are legal but confusing; keep consistent.

### Unpacked struct (TB / model use)

```systemverilog
typedef struct {
    int          cycle_count;
    string       signal_name;
    logic [31:0] value;
} wave_sample_t;  // Not synthesizable (string field)
```

### Union

Used when the same storage needs to be interpreted differently.

```systemverilog
typedef union packed {
    logic [31:0] raw;
    struct packed {
        logic [15:0] hi;
        logic [15:0] lo;
    } halves;
} data32_t;
```

Gotchas:
- Only `packed` unions are synthesizable.
- All members of a packed union must be the same total bit width.
- Unpacked unions are legal in SystemVerilog but not synthesizable.

---

## typedef

Always use `typedef` to name struct, enum, and union types. This enables:
- Reuse across modules (in a package).
- Clean port declarations.
- Readable error messages.

```systemverilog
// In a package:
package my_pkg;
    typedef struct packed {
        logic valid;
        logic [31:0] data;
    } flit_t;
endpackage

// In a module:
import my_pkg::*;
module foo (input flit_t in_flit, output flit_t out_flit);
```

### enum typedef (best practice)

```systemverilog
typedef enum logic [1:0] {
    IDLE  = 2'b00,
    BUSY  = 2'b01,
    DONE  = 2'b10,
    ERROR = 2'b11
} state_t;
```

Gotchas:
- Always specify the base type (`logic [N:0]`) to control bit width and avoid
  tool-dependent defaults.
- Use `unique case` on enums — tools can then warn on unhandled states.
- An uninitialized enum variable starts at 0 in simulation; add a reset in RTL.

---

## Citations

- IEEE 1800-2017 §6.11.2: `logic` type definition and single-driver requirement.
- IEEE 1800-2017 §7.4.1: packed struct bit layout (first-declared field = MSB).
- IEEE 1800-2017 §6.7.1: net vs variable types — the source of the `wire`/`reg` split
  that `logic` resolves.
