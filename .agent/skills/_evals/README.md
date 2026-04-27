# Skill quality evals

Each skill that has rubric-graded baseline scores lives here as
`<skill-name>/evals.json`. The format is `{prompt, expected_output}` pairs —
the prompt is what an engineer would ask, the `expected_output` describes
what a good answer should contain.

## Two ways to run

### 1. Manual rubric (free, no API key required)

Use this if you only have a Claude.ai chat plan. See
[`MANUAL-RUBRIC.md`](MANUAL-RUBRIC.md).

In a Claude Code session:
1. Open the skill's `SKILL.md` and any `references/`.
2. For each prompt in `evals.json`, draft an answer using only the skill's
   content, then compare to `expected_output` and score 0–10.
3. Write results to `<skill-name>/manual-baseline.md`.

### 2. Automated runner (requires Anthropic API key)

```bash
export ANTHROPIC_API_KEY=sk-ant-...
python .agent/skills/_evals/run-quality-eval.py <skill-name>
```

The Anthropic API uses pay-as-you-go credits **separate from any Claude.ai
chat plan**. Get an API key at <https://console.anthropic.com/>.

**Environment variables:**

| Variable | Default | Purpose |
|----------|---------|---------|
| `ANTHROPIC_API_KEY` | (required) | API credentials. |
| `VLSI_EVAL_MODEL` | `claude-sonnet-4-6` | Model used for both candidate generation and judging. |

**CLI flags** (override env):

| Flag | Purpose |
|------|---------|
| `--model NAME` | Set both candidate and judge model. |
| `--candidate-model NAME` | Override candidate only. |
| `--judge-model NAME` | Override judge only. |

**Cost estimate** (5 prompts, single iteration):
- Sonnet: **$0.30–$0.80** per skill
- Opus: **$3–$6** per skill
- Haiku: **$0.05–$0.20** per skill (noisier judging)

**Output layout:**
```
.agent/skills/<skill-name>-workspace/
  iteration-1/
    benchmark.json      # Machine-readable scores
    benchmark.md        # Human-readable summary
  transcripts/
    eval-1.json         # Full prompt/answer/score per eval
    eval-2.json
    ...
```

The `*-workspace/` directories are gitignored except for `benchmark.json`
and `benchmark.md`, so committed history retains scores but not transcripts.

## Comparing Wave 1 rewrites vs baseline

After Wave 1 rewrites a skill, re-run the eval against the new SKILL.md
and rename the output dir to `iteration-2/`. Acceptance criterion (spec §11)
is **non-regression**: the rewrite's average score must be ≥ baseline.

## Authoring new eval prompts

Each prompt should:
- Be answerable from the skill's content alone (don't test for material
  outside the skill's stated scope).
- Have a concrete enough `expected_output` that a judge can score against
  it without ambiguity.
- Cover one of: a common failure pattern, a vendor-specific gotcha, a
  judgment call (when to use X vs Y), or a worked example walkthrough.

5–6 prompts per skill is the target. Fewer than 4 is undersampled; more
than 8 is wasted API spend without proportionate signal.

## Files in this directory

| Path | Purpose |
|---|---|
| `run-quality-eval.py` | The recommended automated runner (rubric scoring). |
| `MANUAL-RUBRIC.md` | Free no-API-spend review process. |
| `run-skill-creator.sh` | Wrapper for skill-creator's discoverability loop — kept for reference but tests a different question (does the skill *trigger* on a query) than rubric scoring. |
| `<skill>/evals.json` | Committed prompt/expected pairs. |
