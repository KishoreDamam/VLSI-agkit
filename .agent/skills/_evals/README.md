# Skill-creator eval harness

This directory holds **committed, reproducible** evaluation prompts and the
runner wrapper for the six Wave 1 core skills. Per spec §7.5, the harness
must be runnable by any contributor — not a one-off run.

## What's here

| Path | Purpose |
|---|---|
| `run-skill-creator.sh` | Wrapper: locates skill-creator, sets paths, runs `scripts.run_loop` |
| `<skill-name>/evals.json` | 5–8 realistic prompts that exercise the skill |
| `<skill-name>/iteration-N/` | Workspace produced by a run (gitignored except `benchmark.md`) |

## Running a baseline (current skill content)

```bash
.agent/skills/_evals/run-skill-creator.sh <skill-name>
# e.g.
.agent/skills/_evals/run-skill-creator.sh fsm-design
```

Output lands in `.agent/skills/<skill-name>-workspace/iteration-N/`. The
iteration counter auto-increments. Each run captures pass-rate, time, tokens.

## Comparing Wave 1 rewrite vs baseline

After Wave 1 rewrites a skill:

```bash
# Re-run with the new SKILL.md
.agent/skills/_evals/run-skill-creator.sh <skill-name>

# Aggregate iteration-1 (baseline) vs iteration-2 (rewrite)
python -m scripts.aggregate_benchmark \
    .agent/skills/<skill-name>-workspace/iteration-2 \
    --skill-name <skill-name>
```

The acceptance criterion (spec §11) is **non-regression**: the rewrite's
pass-rate must be ≥ baseline.

## Re-running an old baseline

The harness is reproducible — anyone can re-run a Wave 1 baseline against
the original committed `evals.json`. Skill-creator pulls the model from the
caller's environment, so absolute scores can drift across model versions;
the **delta** between baseline and rewrite is what we judge against.
