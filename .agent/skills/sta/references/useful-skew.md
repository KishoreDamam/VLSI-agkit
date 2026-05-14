# Useful Skew

> Intentional skew at CTS to redistribute slack between adjacent stages.
> When it's a loan, when it's free, and how to specify it.

## The idea

If stage A has +100 ps of slack and stage B has −50 ps, *delaying* the
clock at the register *between* them shifts the boundary: A's window
shrinks (still positive), B's window grows (now positive).

```
Before:                After useful skew (+80 ps at mid_reg):
  A: +100 ps slack       A: +20 ps slack
  B: −50  ps slack       B: +30 ps slack
                                       ← both pass
```

The total period budget is unchanged — useful skew **redistributes**
margin without adding any.

## When useful skew helps

- **Adjacent stages with opposite slack signs** — classic case, swap
  margin between them.
- **Clock-network capability allows late insertion** — the tool needs
  routing room and buffer headroom to add delay.
- **A specific register can be delayed without breaking downstream
  paths** — only works on registers with positive slack into the *next*
  next stage too.

## When useful skew is a trap

- **Both stages are critical.** Borrowing creates symmetric problems —
  no net gain.
- **Single-cycle paths through a CDC sync chain.** Skewing one register
  in a 2-FF synchronizer destroys MTBF.
- **Hold sensitivity.** Adding clock delay to capture also worsens hold
  on the same path (skew hurts hold). Verify hold post-skew.
- **Multi-fanout register.** Delaying the register's clock affects every
  downstream stage, not just the one you're fixing.

## Two flavors

### Opportunistic useful skew (CTS-driven)

CTS tool decides automatically based on timing reports. Cadence
Innovus: `setCTSMode -opt true`. Synopsys ICC2:
`set_dont_use_ccd false; useful_skew = true`.

Pros: no manual annotation; tool finds the right registers.
Cons: hard to debug if results disappoint; tool may pick paths you'd
prefer to leave alone.

### Directed useful skew

Annotate per-register clock latency:

```tcl
set_clock_latency 0.080 [get_pins mid_reg*/CK]   ;# +80 ps
# or as a hint for CTS
set_clock_latency -source -late 0.080 [get_pins mid_reg*/CK]
```

Pros: explicit, auditable, repeatable.
Cons: requires per-register analysis; needs maintenance as design
changes.

## Constraint: useful skew within balanced tree

Modern CTS tools build *balanced* trees by default — all leaves arrive
at the same time. Useful skew **violates balance intentionally**. Tool
must be told this is allowed:

```tcl
# Cadence Innovus
set_ccopt_property useful_skew true
set_ccopt_property skew_target -slow 0.080

# Synopsys ICC2
set_app_options -name clock_opt.useful_skew -value true
```

Without enabling, the tool will resist adding skew and may revert the
hint.

## Verification

After CTS, audit:

```tcl
report_clock_skew                       ;# expect non-zero, by design
report_timing -path_type full_clock     ;# arrival diff at the skewed reg
report_timing -delay_type min_max       ;# verify hold still passes
```

If hold violations appear at the skewed register, **back off**: useful
skew without hold buffers is a silicon failure.

## Useful skew + CRPR interaction

Useful skew shifts one register's clock arrival, which can **change
which clock buffers are in the common portion** of the launch and
capture paths. CRPR credit may shrink → slack may shrink.

Always re-check `report_crpr` after useful skew. The benefit must
outweigh the CRPR loss.

## Useful skew + latches

Latches with time borrowing already shift effective capture timing.
Adding useful skew on a latch chain is multiply-counted and rarely
worth the complexity. Use one technique or the other.

## Useful skew at sign-off

Most foundry decks **disable opportunistic useful skew** at signoff and
require directed annotations. The reason: opportunistic skew couples
strongly to placement and routing; small ECO changes can erase the
gain. Directed skew is reproducible.

If your flow uses opportunistic skew, document which registers got it
and bound the skew range. ECO scripts must re-validate.

## Worked numerical example

Pre-skew (1 GHz clock):

```
Stage A:  T_cq + T_logic = 850 ps   slack = 1000 − 850 − 50 (setup) − 80 (unc) = +20 ps
Stage B:  T_cq + T_logic = 980 ps   slack = 1000 − 980 − 50 − 80 = −110 ps  ✗
```

Apply useful skew +80 ps at the boundary register:

```
Stage A: capture clock arrives 80 ps later → period for A = 920 ps
         New slack = 920 − 850 − 50 − 80 = −60 ps  ✗
```

That's worse. Useful skew helps only if **A had margin to spare**. Let's
try the example from the top of this doc where A had +100 ps slack:

```
A:  T_cq + T_logic = 770 ps   slack(A) = 1000 − 770 − 50 − 80 = +100 ps
B:  T_cq + T_logic = 920 ps   slack(B) = 1000 − 920 − 50 − 80 = −50 ps   ✗

After +80 ps skew at boundary register:
  Effective period for A = 1000 − 80 = 920 ps → slack(A) = 920 − 770 − 50 − 80 = +20 ps
  Effective period for B = 1000 + 80 = 1080 ps → slack(B) = 1080 − 920 − 50 − 80 = +30 ps ✓
```

Both pass. But notice: A's margin collapsed from 100 to 20 ps. Any
future ECO that tightens A will fail. The useful-skew gain is
*conditional* on A staying loose.

## Common pitfalls

- **Skewing a register on a CDC synchronizer.** Breaks MTBF. Never skew
  sync registers.
- **Skewing a register with high fanout.** All downstream paths see the
  shift; some may go negative.
- **No hold check after skew.** Skew helps setup, hurts hold. Always
  verify hold slack post-skew.
- **Useful skew compensating for under-pipelined RTL.** A 5-LUT critical
  path that "needs" 80 ps of skew really needs another flip-flop.
  Useful skew is for tuning, not for fixing under-design.
- **Trusting `report_clock_skew` to be zero post-CTS.** When useful skew
  is enabled, it *should* be non-zero. Compare against expected values.

## See also

- `setup-hold-equations.md` — skew term in the equation.
- `crpr.md` — useful skew can shrink CRPR credit.
- `clock-uncertainty.md` — uncertainty budgets after skew adjustment.
- `latch-timing.md` — alternative redistribution mechanism.
