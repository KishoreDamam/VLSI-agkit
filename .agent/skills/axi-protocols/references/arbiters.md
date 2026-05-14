# Arbiter Primitives

> Every multi-master AXI interconnect, multi-port scheduler, and shared-
> resource controller eventually needs an arbiter. Five canonical designs,
> their RTL, their fairness properties, and when to reach for each.

## When you need an arbiter

A resource (AXI slave port, FIFO write port, output channel) shared by N
requesters needs an arbiter to pick one. The arbiter takes `req[N-1:0]`
and outputs `grant[N-1:0]` (one-hot — exactly one bit set when at least
one request is asserted).

```
        ┌────────────┐
req[N-1:0] ──→│            │── grant[N-1:0]
              │  ARBITER   │
              │            │
        ┌────────────┐
```

Five common families, each suiting different needs:

| Type | Fairness | Latency | Area | Typical use |
|---|---|---|---|---|
| Fixed-priority | Unfair — req[0] always wins | O(log N) carry | Small | Strict priority (interrupts, error channels) |
| Round-robin | Strong | O(log N) | Small | Default for symmetric AXI masters |
| Matrix | Strong (LRS) | O(1) for grant | O(N²) | Modest N, very low-latency switches |
| Weighted RR | Weighted-strong | O(log N) | Small + weight regs | QoS class with proportional bandwidth |
| Grant-hold | Same as base, extended grant | O(log N) | + 1 reg | Multi-cycle resource holds (cache-line transfers) |

## Fixed-priority arbiter

Simplest. `req[0]` always wins, `req[1]` only if `req[0] = 0`, etc.
Built as a linear carry chain.

```systemverilog
module fixed_pri_arb #(parameter int N = 4) (
    input  logic [N-1:0] req,
    output logic [N-1:0] grant
);
    // c[i] = "no higher-priority request" carry
    logic [N:0] c;
    assign c[0] = 1'b1;
    for (genvar i = 0; i < N; i++) begin : gen_pri
        assign grant[i] = req[i] & c[i];
        assign c[i+1]   = ~req[i] & c[i];
    end
endmodule
```

**Fairness:** none — `req[0]` can starve all others if it never deasserts.

**Use only for:** interrupt prioritization, error channels, debug-mode
masters — situations where strict precedence is *intentional*.

**Carry-chain depth:** linear in N for the simplest form. For N > 8 use
a carry-lookahead variant (same trick as adders) to keep delay
logarithmic.

## Round-robin arbiter — the workhorse

The default arbiter for AXI interconnect arbitration, FIFO write ports,
and most multi-master scenarios. **Strongly fair**: after one grant,
that requester goes to lowest priority; everyone else advances.

The construction has two parts:

1. A **priority generator** — a rotating one-hot vector `p[N-1:0]`
   indicating who has highest priority this cycle.
2. A **cyclic variable-priority arbiter** — picks the highest-priority
   asserted request given the priority vector.

```systemverilog
module rr_arb #(parameter int N = 4) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic [N-1:0] req,
    output logic [N-1:0] grant
);
    // Priority vector — one-hot, rotates after each grant
    logic [N-1:0] p, next_p;

    // Cyclic variable-priority arbiter (combinational)
    // Implementation: replicated carry, OR'd grants (avoids cyclic
    // carry chain that some STA tools refuse to time)
    logic [N-1:0] req_masked_a, grant_a;  // first pass — high priorities first
    logic [N-1:0] req_masked_b, grant_b;  // second pass — wrap-around
    logic [N:0]   c_a, c_b;

    // Pass A: only requests at or after the priority pointer
    assign c_a[0] = 1'b0;
    for (genvar i = 0; i < N; i++) begin : gen_a
        wire enable = p[i] | c_a[i];          // becomes 1 at the priority bit
        assign grant_a[i] = req[i] & enable;
        assign c_a[i+1]   = enable & ~req[i];
    end

    // Pass B: wrap — anyone with no winner above
    wire none_in_a = ~|grant_a;
    assign c_b[0] = none_in_a;
    for (genvar i = 0; i < N; i++) begin : gen_b
        assign grant_b[i] = req[i] & c_b[i];
        assign c_b[i+1]   = c_b[i] & ~req[i];
    end

    assign grant = grant_a | grant_b;

    // Priority advances after a grant
    assign next_p = (|grant) ? {grant[N-2:0], grant[N-1]}   // rotate p to next-after-winner
                             : p;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)        p <= {{(N-1){1'b0}}, 1'b1};      // start at bit 0
        else               p <= next_p;
    end
endmodule
```

**Why the two-pass form?** The naïve cyclic form has a carry chain that
loops (`c[0] = c[N]`), which some STA tools refuse to time. Splitting
into "above priority" and "wrap" passes breaks the cycle while
preserving the semantics.

**Fairness:** strong. If requester `i` is just served, it cannot win
again until every other asserted requester has had a turn.

**Critical-path:** linear in N for both passes; use carry-lookahead for
N > 8.

## Round-robin variants

### Mask-based round-robin (cleaner alternative)

```systemverilog
// Mask all requesters at priority and below; pick lowest of remaining
wire [N-1:0] mask = (p - 1'b1);                  // bits below priority
wire [N-1:0] req_high = req & ~mask;
wire [N-1:0] req_low  = req &  mask;

// Lowest-bit-of vector via isolate-lowest-1 trick
wire [N-1:0] grant_high = req_high & (~req_high + 1'b1);
wire [N-1:0] grant_low  = req_low  & (~req_low  + 1'b1);

assign grant = (|req_high) ? grant_high : grant_low;
```

Often produces smaller, faster netlists than the carry-chain form on
modern synthesizers. Same fairness properties.

### Update priority on grant or on request?

Two policies:

- **On-grant update**: `p` advances only when a grant happens. Idle
  cycles don't rotate. Strong fairness preserved exactly.
- **On-clock update**: `p` rotates every cycle. Implementation simpler.
  Strong fairness still holds but with up to N − 1 cycles of "skip"
  on idle priorities.

Default to on-grant for AXI arbitration — predictable, lowest
contention-cycle count.

## Matrix arbiter — least-recently-served

State is an `N × N` upper-triangular bit array `w[i][j]` (`i < j`).
`w[i][j] = 1` means "requester `i` outranks requester `j`". Each grant
to requester `k`:

- Clears row `k`: every `w[k][j] := 0` (now k is lowest priority).
- Sets column `k`: every `w[i][k] := 1` (everyone else outranks k).

```systemverilog
module matrix_arb #(parameter int N = 4) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic [N-1:0] req,
    output logic [N-1:0] grant
);
    // Priority matrix: w[i][j] = 1 means i has priority over j (i<j only stored)
    logic [N-1:0][N-1:0] w;

    // Request i is "blocked" if any higher-ranked j is requesting
    logic [N-1:0] blocked;
    always_comb begin
        for (int i = 0; i < N; i++) begin
            blocked[i] = 1'b0;
            for (int j = 0; j < N; j++) begin
                if (i != j) begin
                    // j outranks i if (j<i and w[j][i]) or (j>i and ~w[i][j])
                    automatic logic j_wins;
                    j_wins = (j < i) ? w[j][i] : ~w[i][j];
                    if (req[j] & j_wins) blocked[i] = 1'b1;
                end
            end
        end
    end

    assign grant = req & ~blocked;

    // Update priorities on grant
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Initial: lower index outranks higher (like fixed-pri start state)
            for (int i = 0; i < N; i++)
                for (int j = i+1; j < N; j++) w[i][j] <= 1'b1;
        end else begin
            for (int k = 0; k < N; k++) begin
                if (grant[k]) begin
                    // Clear row k (k now lowest), set column k (everyone outranks k)
                    for (int j = k+1; j < N; j++) w[k][j] <= 1'b0;
                    for (int i = 0; i < k;   i++) w[i][k] <= 1'b1;
                end
            end
        end
    end
endmodule
```

**Fairness:** strong, LRS (least-recently-served). The longest-waiting
requester always wins.

**Area:** `O(N²)` flops in the priority matrix. Practical for `N ≤ 16`;
expensive beyond that.

**Latency:** the grant is `req & ~blocked` — pure combinational, single
gate-stage of OR (across the row) and AND. Lowest-latency option for
small N.

**Use when:** N is modest (4–16), latency matters, fairness must be
strict, and area is not the bottleneck.

## Weighted round-robin

Each requester `i` has a weight `w[i]`. Over a window of `Σw[i]` grants,
requester `i` gets exactly `w[i]` grants.

Architecture: counter per requester, decrement on grant, mask out when
counter hits zero, reset all counters when no requester has quota left.

```systemverilog
module wrr_arb #(parameter int N = 4, parameter int W = 4) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic [N-1:0] req,
    input  logic [W-1:0] weight [N],    // per-requester weight
    output logic [N-1:0] grant
);
    logic [W-1:0] count [N];
    logic [N-1:0] eligible;
    logic         all_done;

    // Eligible if count > 0
    for (genvar i = 0; i < N; i++)
        assign eligible[i] = req[i] & (count[i] != '0);

    assign all_done = ~|((|req ? eligible : '0));   // no eligible left this round

    // Pick winner from eligible set via round-robin
    rr_arb #(.N(N)) u_rr (.clk(clk), .rst_n(rst_n),
                          .req(eligible), .grant(grant));

    // Counter management
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < N; i++) count[i] <= weight[i];
        end else begin
            // Decrement winner's count
            for (int i = 0; i < N; i++)
                if (grant[i]) count[i] <= count[i] - 1'b1;
            // Reset all counters when no eligible requester remains
            if (all_done)
                for (int i = 0; i < N; i++) count[i] <= weight[i];
        end
    end
endmodule
```

**Fairness:** weighted-strong. Over each window of `Σ weight` grants,
each requester is served exactly `weight[i]` times.

**Burstiness trade-off:** large weights → long windows → more
burstiness within a window. A requester with `weight = 8` may get 8
consecutive grants before another reclaims. If burstiness matters,
prefer smaller weights and faster cycling.

**Use for:** QoS classes (best-effort vs guaranteed), AXI ports with
different SLAs, DMA engines competing on a shared FIFO with bandwidth
contracts.

## Grant-hold extension

Adds a `hold[i]` input alongside `req[i]`. Once requester `i` is
granted, if `hold[i]` stays asserted, the grant *sticks* — no new
arbitration until `hold[i]` deasserts.

```systemverilog
module grant_hold_wrapper #(parameter int N = 4) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic [N-1:0] req,
    input  logic [N-1:0] hold,
    output logic [N-1:0] grant
);
    logic [N-1:0] last_grant;
    logic [N-1:0] base_grant;
    logic [N-1:0] held;
    logic         any_hold;

    rr_arb #(.N(N)) u_arb (.clk(clk), .rst_n(rst_n),
                            .req(req & ~{N{any_hold}}),  // suppress while held
                            .grant(base_grant));

    assign held     = last_grant & hold;
    assign any_hold = |held;
    assign grant    = any_hold ? held : base_grant;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) last_grant <= '0;
        else        last_grant <= grant;
endmodule
```

**Use for:** AXI burst transfers (master holds for entire AWLEN+1
beats), cache-line transfers, atomic operations that must not be
interrupted.

**Caveat:** grant-hold breaks strong fairness — a malicious requester
can hold indefinitely. Pair with a max-hold-cycles timeout for
safety-critical systems.

## Selection guide

```
Decision: which arbiter?

  ┌─ Need strict priority? (interrupts, errors)
  │     YES ──→ fixed-priority arbiter
  │
  ├─ N ≤ 16 AND latency matters AND area OK?
  │     YES ──→ matrix arbiter
  │
  ├─ Different bandwidth contracts per requester?
  │     YES ──→ weighted round-robin
  │
  ├─ Multi-cycle holds needed (burst transfers)?
  │     YES ──→ round-robin + grant-hold wrapper
  │
  └─ Default ────→ round-robin (mask-based form for N > 8)
```

## AXI interconnect application

A typical 4-master / 4-slave AXI4 interconnect uses arbiters at:

1. **Address channels (AW, AR)** — per-slave arbiter picks one master.
   Use **round-robin**; latency low, fairness essential.
2. **Write data (W)** — must follow whichever master won AW for that
   slave; **grant-hold wrapper** around RR, holding until WLAST.
3. **Response channels (B, R)** — per-master arbiter picks one slave.
   Round-robin again; per-master ID tracking handles ordering.

For QoS-enabled designs, replace the M-side RR with **weighted RR**
keyed off AxQOS.

## Common pitfalls

- **Round-robin priority not updating on idle cycles** — fairness still
  holds, but cycle-by-cycle burstiness can surprise system-level
  analysis.
- **Fixed-priority arbiter on a shared bus** — starvation in
  silicon; lint should flag it on every multi-master interconnect.
- **Matrix arbiter sized for N > 16** — quadratic area; switch to
  hierarchical round-robin.
- **Grant-hold without max-hold timeout** — DoS vector inside the
  chip; one stuck master starves all others.
- **Weighted RR with weight = 0** for any requester — that requester
  is silently never served. Either give every requester ≥ 1 weight or
  use an explicit "disable" mux.
- **Synthesis flattening the carry chain** when you wanted hierarchical
  structure — for N > 8, force structural carry-lookahead via
  `keep_hierarchy` or use the mask-based form.

## Verification checklist

- **Fairness assertion**: after any single requester wins, every other
  asserted requester must win within ≤ N cycles (round-robin) or
  unbounded (fixed-priority — assertion expected to fail).
- **No double-grant**: assert `$onehot0(grant)` every cycle.
- **Grant implies request**: assert `(grant & ~req) == 0`.
- **Grant within 1 cycle of any request**: assert `(|req) |-> ##[0:1]
  (|grant)` (for combinational arbiters, 0 delay).
- **Grant-hold safety**: max-hold-cycles bounded by an assertion timer.

## Citations

- **Dally & Towles**, *Principles and Practices of Interconnection
  Networks*, Morgan Kaufmann 2004, Chapter 18 — fixed-priority,
  variable-priority, round-robin, matrix, weighted RR, grant-hold.
- **ARM IHI 0022H** — AMBA AXI Protocol Specification (interconnect
  arbitration requirements).
- **Synopsys DesignWare DW_axi** — round-robin and weighted-RR
  arbiter reference implementations.

## See also

- `fsm-design` skill — state machines that often hide arbitration
  logic.
- `synthesis-guidelines/references/retiming-and-register-balancing.md`
  — retiming concerns when arbiter state is split across pipeline
  stages.
- `clean-rtl/references/simulation-race.md` — multi-driver hazards in
  arbiter outputs.
- `sta` skill — for closure on multi-stage arbiters on the critical
  path.
