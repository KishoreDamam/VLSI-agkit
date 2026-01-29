---
name: fsm-design
description: State machine patterns, encoding, and implementation techniques.
---

# FSM Design

> State machine patterns for reliable RTL design.

---

## FSM Coding Styles

### Two-Process FSM (Recommended)

```systemverilog
typedef enum logic [1:0] {
    IDLE   = 2'b00,
    RUN    = 2'b01,
    DONE   = 2'b10
} state_t;

state_t state, next_state;

// Sequential: State register
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        state <= IDLE;
    else
        state <= next_state;
end

// Combinational: Next state logic
always_comb begin
    next_state = state;  // Default: hold
    case (state)
        IDLE: if (start) next_state = RUN;
        RUN:  if (done)  next_state = DONE;
        DONE:            next_state = IDLE;
        default:         next_state = IDLE;
    endcase
end
```

### Three-Process FSM

```systemverilog
// Process 1: State register
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) state <= IDLE;
    else        state <= next_state;
end

// Process 2: Next state logic
always_comb begin
    next_state = state;
    case (state)
        IDLE: if (start) next_state = RUN;
        // ...
    endcase
end

// Process 3: Output logic
always_comb begin
    busy = 1'b0;
    case (state)
        RUN: busy = 1'b1;
    endcase
end
```

---

## State Encoding

| Encoding | Bits | Use Case |
|----------|------|----------|
| Binary | log2(N) | Area efficient |
| One-hot | N | Speed, FPGA |
| Gray | log2(N) | CDC, low power |

### One-Hot (FPGA Preferred)

```systemverilog
typedef enum logic [3:0] {
    IDLE = 4'b0001,
    RUN  = 4'b0010,
    WAIT = 4'b0100,
    DONE = 4'b1000
} state_t;

// Use state bits directly
assign busy = state[1] | state[2];  // RUN or WAIT
```

---

## Output Types

### Moore (Output depends on state only)

```systemverilog
always_comb begin
    case (state)
        IDLE: out = 1'b0;
        RUN:  out = 1'b1;
        DONE: out = 1'b0;
    endcase
end
```

### Mealy (Output depends on state + input)

```systemverilog
always_comb begin
    out = 1'b0;
    case (state)
        IDLE: out = start;  // Combinational path
        RUN:  out = 1'b1;
    endcase
end
```

### Registered Outputs (Best for Timing)

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        out <= 1'b0;
    end else begin
        case (next_state)  // Use next_state
            RUN:  out <= 1'b1;
            default: out <= 1'b0;
        endcase
    end
end
```

---

## Common Patterns

### Counter with FSM

```systemverilog
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state <= IDLE;
        count <= '0;
    end else begin
        case (state)
            IDLE: begin
                if (start) begin
                    state <= COUNT;
                    count <= '0;
                end
            end
            COUNT: begin
                if (count == MAX_COUNT)
                    state <= DONE;
                else
                    count <= count + 1;
            end
            DONE: state <= IDLE;
        endcase
    end
end
```

### Handshake FSM

```systemverilog
typedef enum logic [1:0] {
    IDLE, REQ, WAIT_ACK, COMPLETE
} state_t;

always_comb begin
    next_state = state;
    req = 1'b0;
    
    case (state)
        IDLE: begin
            if (send) next_state = REQ;
        end
        REQ: begin
            req = 1'b1;
            next_state = WAIT_ACK;
        end
        WAIT_ACK: begin
            req = 1'b1;
            if (ack) next_state = COMPLETE;
        end
        COMPLETE: begin
            next_state = IDLE;
        end
    endcase
end
```

---

## Best Practices

| Practice | Reason |
|----------|--------|
| Use enums | Readability |
| Include default case | Avoid latches, recovery |
| Default next_state = state | Hold on undefined |
| Register outputs | Better timing |
| Assert on illegal states | Catch bugs |

---

## Assertions for FSMs

```systemverilog
// No illegal states
always @(posedge clk) begin
    assert (state inside {IDLE, RUN, DONE})
        else $error("Illegal state");
end

// Eventually leaves IDLE
property p_exit_idle;
    @(posedge clk) disable iff (!rst_n)
    (state == IDLE && start) |-> ##[1:10] (state != IDLE);
endproperty
assert property (p_exit_idle);
```
